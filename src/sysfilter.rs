#![allow(non_snake_case)]

use std::fs::{self, File};
use std::io::Write;
use serde_json::{Value, Map};
use serde::{Serialize, Deserialize};
use std::process::Command;
use std::collections::HashMap;
use std::collections::HashSet;

#[derive(Serialize, Deserialize, Debug)]
pub struct Module {
    pub has_symbols:    bool,
    pub path:           String,
}

/// Module name to Module hashmap
#[derive(Serialize, Deserialize, Debug)]
pub struct Scope(pub HashMap<String, Module>);

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Symbol {
    pub module: String,
    pub name:   String,
}

#[derive(Debug)]
pub struct InitialAnalysis {
    pub scope: Scope,
    pub indirect_targets: HashSet<Symbol>,
    pub indirect_targets_string: Vec<String>,
    pub thread_entry_points : Vec<Symbol>,
    pub fork_callers: Vec<Symbol>,
    pub direct_edges: Map<String, Value>,
    pub syscalls: Vec<u64>,
    pub callgraph: HashSet<Symbol>
}

#[derive(Debug)]
pub struct PrunedAnalysis {
    pub syscalls: Vec<u64>,
    pub indirect_targets: Vec<String>,
}

pub fn initial_sysfilter_analysis(sysfilter_path: &str,
                                  binary_path: &str,
                                  output_path: &str) -> InitialAnalysis {
    // Execute Sysfilter
    Command::new(sysfilter_path)
        .args(["--full-json", "--arg-mode", "--dump-fcg", "-o", output_path, binary_path])
        .spawn()
        .expect("Failed to execute sysfilter")
        .wait().expect("Failed to wait for sysfilter");
    
    // Load the json output
    let json_data = load_json(output_path);

    // Deserialize the analysis scope
    let scope: Scope = serde_json::from_value(json_data["analysis_scope"].to_owned()).unwrap();

    // Get syscalls
    let syscalls_json = json_data["syscalls"].as_array().unwrap();
    let mut syscalls = vec!();
    for x in syscalls_json {
        syscalls.push(x.as_u64().unwrap());
    }

    // Deserialize indirect targets
    let indirect_targets = &json_data["vacuum"]["analysis"]["all"]["callgraph"]["indirect_targets"]
        .as_array().unwrap();

    let mut indirect_targets_set = HashSet::new();

    for indirect_target in *indirect_targets {
        let indirect_target = indirect_target.as_str().unwrap().to_owned();
        let tokens: Vec<&str> = indirect_target.split(|c| c == '@' || c == '+').collect();
        let module_name = tokens[0];
        let function_name = tokens[1];

        indirect_targets_set.insert(Symbol {
            module: module_name.to_owned(),
            name: function_name.to_owned(),
        });
    }
    
    // Also a string version of the indirect targets for logging

    let mut indirect_targets_str = vec!();

    for indirect_target in *indirect_targets {
        let indirect_target = indirect_target.as_str().unwrap().to_owned();
        indirect_targets_str.push(indirect_target);
    }

    // Find thread entry points
    let mut thread_entry_points = vec!();
    let argtrack_data = &json_data["vacuum"]["analysis"]["all"]["arg_track_values"]
        .as_array().unwrap();

    for argtrack_entry in *argtrack_data {
        let target_function = argtrack_entry["target_function"].as_str().unwrap().to_owned();
        let target_function = target_function.split('@').collect::<Vec<&str>>()[0];
        if target_function == "pthread_create" {
            let function_name = argtrack_entry["function_from_value"].as_str();
            let module_name = argtrack_entry["module_from_value"].as_str();
            match (function_name, module_name) {
                (Some(function), Some(module)) => {
                    thread_entry_points.push(Symbol {
                        module: module.to_owned(),
                        name: function.to_owned(),
                    });
                },
                _ => ()
            }
        }

    }

    // Find Direct edges
    let direct_edges = &json_data["vacuum"]["analysis"]["all"]["callgraph"]["direct_edges"]
        .as_object().unwrap();
    // Find fork callers
    let mut fork_callers = vec!();
    for (fun, edges) in *direct_edges {
        let edges = edges.as_array().unwrap();
        for x in edges {
            let x = x.as_str().unwrap();
            let tokens: Vec<&str> = x.split(|c| c == '@' || c == '+').collect();
            let function_name = tokens[1];
            if function_name == "fork" || function_name == "fork_compat" {
                let tokens: Vec<&str> = fun.split(|c| c == '@' || c == '+').collect();
                let module_name = tokens[0];
                let function_name = tokens[1];
                if function_name != "fork" && function_name != "fork_compat" {
                    println!("FOUND A FORK CALLER : {:?}", fun);
                    fork_callers.push(Symbol {
                        module: module_name.to_owned(),
                        name: function_name.to_owned(),
                    });
                }
            }
        }
    }


    // Find all functions in callgraph
    let mut callgraph = HashSet::new();
    let funcs = &json_data["vacuum"]["analysis"]["all"]["callgraph"]["funcs"]
        .as_object().unwrap();
    for (f, _) in *funcs {
        let f = f.as_str().to_owned();
        let tokens: Vec<&str> = f.split(|c| c == '@' || c == '+').collect();
        let module_name = tokens[0];
        let function_name = tokens[1];

        callgraph.insert(Symbol {
            module: module_name.to_owned(),
            name: function_name.to_owned(),
        });
    }


    InitialAnalysis {
        scope: scope,
        indirect_targets: indirect_targets_set,
        indirect_targets_string: indirect_targets_str,
        thread_entry_points,
        fork_callers,
        direct_edges: (*direct_edges).to_owned(),
        syscalls,
        callgraph,
    }
}

pub fn pruned_sysfilter_analysis(sysfilter_path: &str,
                                  binary_path: &str,
                                  output_path: &str,
                                  authorized_fct_path: &str) -> PrunedAnalysis 
{
    // Execute Sysfilter
    Command::new(sysfilter_path)
        .args(["--full-json", "--dump-fcg", "--atpruned-fcg", "--pruned-ATs-file", authorized_fct_path, "-o", output_path, binary_path])
        .spawn()
        .expect("Failed to execute sysfilter with pruning")
        .wait().expect("Failed to wait for sysfilter (with pruning)");

    // Load the json output
    let json_data = load_json(output_path);
    // Get syscalls
    let syscalls_json = json_data["syscalls"].as_array().unwrap();

    let mut syscalls = vec!();
    for x in syscalls_json {
        syscalls.push(x.as_u64().unwrap());
    }

    let indirect_targets = &json_data["init"]["analysis"]["all"]["callgraph"]["indirect_targets"]
        .as_array().unwrap();
    
    let mut indirect_targets_vec = vec!();

    for indirect_target in *indirect_targets {
        let indirect_target = indirect_target.as_str().unwrap().to_owned();
        indirect_targets_vec.push(indirect_target);
    }

    PrunedAnalysis {
        syscalls,
        indirect_targets: indirect_targets_vec,
    }
}

fn get_DCG_rec_helper(direct_edges: &Map<String, Value>, root: String, DCG: &mut HashSet<String>) {
    DCG.insert(root.to_owned());
    match direct_edges.get(&root) {
        Some(edges) => {
            for fun in edges.as_array().unwrap() {
                if !DCG.contains(fun.as_str().unwrap()) { 
                    get_DCG_rec_helper(direct_edges, fun.as_str().unwrap().to_owned(), DCG);
                }
            }
        }
        None => {return;}
    }
}

pub fn get_DCG_string(direct_edges: &Map<String, Value>, root: &Symbol) -> HashSet<String> {
    let mut DCG = HashSet::new();
    DCG.insert(format!("{}@{}+0", root.module, root.name));
    for (fun, edges) in direct_edges {
        let tokens: Vec<&str> = fun.split(|c| c == '@' || c == '+').collect();
        let module_name = tokens[0];
        let function_name = tokens[1];
        if function_name == root.name && module_name == root.module {
            for fun in edges.as_array().unwrap() {
                get_DCG_rec_helper(direct_edges, fun.as_str().unwrap().to_owned(), &mut DCG);
            }
        }
    }
    return DCG;
}


pub fn get_DCG(direct_edges: &Map<String, Value>, root: &Symbol) -> HashSet<Symbol> {
    let mut DCG = HashSet::new();
    let dcg_string = get_DCG_string(direct_edges, root);
    for fun in dcg_string {
        let tokens: Vec<&str> = fun.split(|c| c == '@' || c == '+').collect();
        let module_name = tokens[0];
        let function_name = tokens[1];

        DCG.insert(Symbol {
            module: module_name.to_owned(),
            name: function_name.to_owned(),
        });
    }
    DCG
}

fn load_json(path: &str) -> Value {
    let data = fs::read_to_string(path).expect("Failed to read json file");
    let json_data: Value = serde_json::from_str(&data).expect("Failed to decode json");
    return json_data;
}

pub fn write_authorized_functions_json(json_name: &str, fun_set: &HashSet<Symbol>) {
    let mut file = File::create(json_name)
        .expect("Failed to create authorized ATs json file");
    file.write_all(b"[").unwrap();
    for (i, fun) in fun_set.iter().enumerate() {
        write!(file, "{{\"module\": \"module-{}\", \"function\" : \"{}\"}}", fun.module, fun.name)
            .unwrap();
        if i != fun_set.len() - 1 {
            file.write_all(b", ").unwrap();
        }
    }
    file.write_all(b"]").unwrap();
}
