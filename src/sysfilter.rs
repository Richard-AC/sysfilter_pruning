use std::fs;
use serde_json::{Value, Map};
use serde::{Serialize, Deserialize};
use std::process::Command;
use std::collections::HashMap;
use std::collections::HashSet;

//#[derive(Debug)]
#[derive(Serialize, Deserialize, Debug)]
pub struct Module {
    pub has_symbols:    bool,
    pub path:           String,
}

/// Module name to Module hashmap
//#[derive(Debug)]
#[derive(Serialize, Deserialize, Debug)]
pub struct Scope(pub HashMap<String, Module>);

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct Symbol {
    pub module: String,
    pub name:   String,
}

#[derive(Debug)]
pub struct InitialAnalysis {
    pub scope: Scope,
    pub indirect_targets: Vec<Symbol>,
    pub thread_entry_points : Vec<Symbol>,
    pub direct_edges: Map<String, Value>,
}

pub fn initial_sysfilter_analysis(sysfilter_path: &str,
                                  binary_path: &str,
                                  output_path: &str) -> InitialAnalysis {
    // Execute Sysfilter
    /*
    Command::new(sysfilter_path)
        .args(["--full-json", "--arg-mode", "--dump-fcg", "-o", output_path, binary_path])
        .spawn()
        .expect("Failed to execute sysfilter")
        .wait().expect("Failed to wait for sysfilter");*/
    
    // Load the json output
    let json_data = load_json(output_path);

    // Deserialize the analysis scope
    let scope: Scope = serde_json::from_value(json_data["analysis_scope"].to_owned()).unwrap();
    println!("{:#?}", scope);

    // Deserialize indirect targets
    let indirect_targets = &json_data["vacuum"]["analysis"]["all"]["callgraph"]["indirect_targets"]
        .as_array().unwrap();

    let mut indirect_targets_vec = vec!();

    for indirect_target in *indirect_targets {
        let indirect_target = indirect_target.as_str().unwrap().to_owned();
        let tokens: Vec<&str> = indirect_target.split(|c| c == '@' || c == '+').collect();
        let module_name = tokens[0];
        let function_name = tokens[1];

        indirect_targets_vec.push(Symbol {
            module: module_name.to_owned(),
            name: function_name.to_owned(),
        });
    }

    // Find thread entry points
    let mut thread_entry_points = vec!();
    let argtrack_data = &json_data["vacuum"]["analysis"]["all"]["arg_track_values"]
        .as_array().unwrap();

    for argtrack_entry in *argtrack_data {
        let target_function = argtrack_entry["target_function"].as_str().unwrap().to_owned();
        let target_function = target_function.split('@').collect::<Vec<&str>>()[0];
        if target_function == "pthread_create" {
            let function_name = argtrack_entry["function_from_value"].as_str().unwrap().to_owned();
            let module_name = argtrack_entry["module_from_value"].as_str().unwrap().to_owned();
            thread_entry_points.push(Symbol {
                module: module_name,
                name: function_name,
            })
        }

    }

    // Find fork callers
    // TODO


    // Find Direct edges
    let direct_edges = &json_data["vacuum"]["analysis"]["all"]["callgraph"]["direct_edges"]
        .as_object().unwrap();


    /*
    // Example of getting the DCG for a given root
    let sym = Symbol {module: String::from("(executable)"), name: String::from("main")};
    let dcg = get_DCG(direct_edges, sym);
    println!("{:?}", dcg);
    panic!();
    */

    InitialAnalysis {
        scope: scope,
        indirect_targets: indirect_targets_vec,
        thread_entry_points,
        direct_edges: (*direct_edges).to_owned(),
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

pub fn get_DCG(direct_edges: &Map<String, Value>, root: Symbol) -> HashSet<String> {
    let mut DCG = HashSet::new();
    DCG.insert(format!("{}@{}+0", root.module, root.name));
    for (fun, edges) in direct_edges {
        let tokens: Vec<&str> = fun.split(|c| c == '@' || c == '+').collect();
        let module_name = tokens[0];
        let function_name = tokens[1];
        if function_name == root.name && module_name == root.module {
            for fun in edges.as_array().unwrap() {
                //println!("{}", fun);
                get_DCG_rec_helper(direct_edges, fun.as_str().unwrap().to_owned(), &mut DCG);
            }
        }
    }
    return DCG;
}

fn load_json(path: &str) -> Value {
    let data = fs::read_to_string(path).expect("Failed to read json file");
    let json_data: Value = serde_json::from_str(&data).expect("Failed to decode json");
    return json_data;
}
