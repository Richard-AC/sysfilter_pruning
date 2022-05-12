#![allow(non_snake_case)]

use core::fmt::LowerHex;
use object::{Object, ObjectSection};
use std::collections::{HashMap, HashSet};
use std::{borrow, env, fs};
use std::borrow::Cow;
use std::process::Command;
use std::fs::File;
use std::io::Write;

use gimli::{Dwarf, Reader, Unit, UnitOffset};
use gimli::DebuggingInformationEntry;
use gimli::EndianSlice;

use memmap::Mmap;

use sysfilter_pruning::sysfilter::{self, Symbol, InitialAnalysis, PrunedAnalysis};

/// Dwarf info of each module
#[derive(Debug)]
struct DwarfinfoDict<R>(HashMap::<String, Dwarf<R>>);

#[derive(Debug)]
struct MmapDict(HashMap::<String, Mmap>);

/// The type of a function
#[derive(Debug, PartialEq, Eq, Hash)]
struct FunctionType {
    return_type: VariableType,
    arguments_types: Vec<VariableType>,
}

/// The type of a variable
#[derive(Debug, PartialEq, Eq, Hash)]
struct VariableType(Vec<TypeToken>);

impl VariableType {
    // Append tokens from other to self
    fn add_tokens(&mut self, other: &mut VariableType) {
        self.0.append(&mut other.0);
    }
}

/// Tokens that may appear in a type
#[derive(Debug, PartialEq, Eq, Hash)]
enum TypeToken {
    /// A name e.g int
    Name(String),
    //Union,
    Pointer,
    Const,
    //Enum,
    Void,
    Function(FunctionType)
}

/// Represents the types that have already been seen in each module/
/// This is used to avoid finding function pointers in the same type
/// multiple times
#[derive(Debug)]
struct DejavuSets(HashMap<String, HashSet<usize>>);

impl DejavuSets {
    /// Initializes the DejavuSets given the names of the modules
    fn new(modules: Vec<&String>) -> Self {
        let mut dejavusets = HashMap::new();
        for name in modules {
            dejavusets.insert(
                name.to_owned(),
                HashSet::new());
        }
        DejavuSets(dejavusets)
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 4 {
        println!("Usage: {} <sysfilter_path> <output_path> <binary_path>", args[0]);
        return;
    }

    let sysfilter_path = &args[1];
    let output_path  = &args[2]; 
    let binary_path = &args[3]; 

    let binary_name = binary_path.split('/').collect::<Vec<_>>();
    let output_json = format!("{}{}", binary_name.last().unwrap(), "_sysfilter.json");

    let initial_analysis = sysfilter::initial_sysfilter_analysis(
        sysfilter_path,
        binary_path,
        &output_json);
    //println!("Initial analysis : {:#?}", initial_analysis);
    
    // Load the dwarf data in a really weird way to make to borrow checker happy
    // Mmap all the files in scope
    let mut mmap_dict: MmapDict = MmapDict (HashMap::new());
    for (module_name, scope_entry) in &initial_analysis.scope.0 {
        if !scope_entry.has_symbols {
            //panic!("No symbols for {}", module_name);
            println!("No symbols for {}", module_name);
            continue;
        }
        println!("Loading dwarf of {}", module_name);

        // Separate debug info can be in many places
        // We use gdb to find it for us
        let gdb_output = Command::new("gdb")
            .args(["-ex", "q", "-q", &scope_entry.path])
            .output()
            .expect("Failed to run gdb");
        let gdb_output = String::from_utf8_lossy(&gdb_output.stdout);
        let debug_paths = gdb_output.split('\n')
            .filter(|s| s.starts_with("Reading symbols from"))
            .map(|s| s.split(' ').collect::<Vec<_>>()[3])
            .map(|s| &s[..s.len()-3])
            .collect::<Vec<&str>>();

        for debug_path in &debug_paths {
            println!("{:?}", debug_path);
        }

        let path = debug_paths.last().unwrap();

        let file = fs::File::open(&path).unwrap();
        let mmap = unsafe { memmap::Mmap::map(&file).unwrap() };
        mmap_dict.0.insert (
            module_name.to_owned(),
            mmap);
    }

    // Load dwarf as Cow
    let mut dwarfinfo_dict_cow: DwarfinfoDict<Cow<[u8]>> = DwarfinfoDict(HashMap::new());
    for (module_name, mmap) in &mmap_dict.0 {
        let object = object::File::parse(&**mmap).unwrap();
        // Load dwarf info 
        let load_section = |id: gimli::SectionId| -> Result<borrow::Cow<[u8]>, gimli::Error> {
            match object.section_by_name(id.name()) {
                Some(ref section) => Ok(section
                    .uncompressed_data()
                    .unwrap_or(borrow::Cow::Borrowed(&[][..]))),
                None => Ok(borrow::Cow::Borrowed(&[][..])),
            }
        };
        // Load all of the sections.
        let dwarf_cow = gimli::Dwarf::load(&load_section).unwrap();
        dwarfinfo_dict_cow.0.insert(
            module_name.to_owned(),
            dwarf_cow);
    }

    let mut dwarf_dict: DwarfinfoDict<EndianSlice<gimli::RunTimeEndian>> = DwarfinfoDict(HashMap::new());
    for (module_name, mmap) in &mmap_dict.0 {
        let object = object::File::parse(&**mmap).unwrap();
        let endian = if object.is_little_endian() {
            gimli::RunTimeEndian::Little
        } else {
            gimli::RunTimeEndian::Big
        };
        let dwarf_cow = &dwarfinfo_dict_cow.0[module_name];
        // Borrow a `Cow<[u8]>` to create an `EndianSlice`.
        let borrow_section: &dyn for<'a> Fn(
            &'a borrow::Cow<[u8]>,
        ) -> gimli::EndianSlice<'a, gimli::RunTimeEndian> =
            &|section| gimli::EndianSlice::new(&*section, endian);

        // Create `EndianSlice`s for all of the sections.
        let dwarf = dwarf_cow.borrow(&borrow_section);
        dwarf_dict.0.insert(
            module_name.to_owned(),
            dwarf);
    }

    let mut dejavu_sets = DejavuSets::new(initial_analysis.scope.0.keys().collect::<Vec<_>>());


    find_relevant_CUs(&dwarf_dict, &initial_analysis);

    // Finding function pointers in global variables
    let fun_ptrs_types_in_globals = 
        find_function_pointer_types_in_globals(&dwarf_dict, &mut dejavu_sets);
    //println!("fun ptrs types in globals {:?}", fun_ptrs_types_in_globals);

    // Find function types of indirect_targets
    let mut at_function_types = HashMap::new();
    for (module_name, _) in &initial_analysis.scope.0 {
        // If we have DWARF info for this module
        if dwarf_dict.0.contains_key(module_name) {
            at_function_types.extend(
                find_all_function_types(&dwarf_dict.0[module_name], 
                                        &module_name, 
                                        &initial_analysis.indirect_targets));
        }
    }
    // Add all the AT functions in modules for which we don't have symbols
    for fun in &initial_analysis.indirect_targets {
        if !at_function_types.contains_key(&fun) {
            at_function_types.insert(fun.clone(), None);
        }
    }

    //println!("AT function types {:#?}", at_function_types);

    let mut results = HashMap::new();

    let entry = Symbol {module: String::from("libc.so.6"), name: String::from("__libc_start_main")};
    println!("Entry point : {:?}", entry);
    let res = analyze_one_entry_point(&dwarf_dict, &mut dejavu_sets, &entry, &initial_analysis, &fun_ptrs_types_in_globals, &at_function_types, binary_path, sysfilter_path);
    println!("Syscalls len {}", res.syscalls.len());
    results.insert(entry, res);

    for thread_entry in &initial_analysis.thread_entry_points {
        println!("Entry point : {:?}", thread_entry);
        let res = analyze_one_entry_point(&dwarf_dict, &mut dejavu_sets, thread_entry, &initial_analysis, &fun_ptrs_types_in_globals, &at_function_types, binary_path, sysfilter_path);
        println!("Syscalls len {}", res.syscalls.len());
        results.insert(thread_entry.clone(), res);
    }

    for fork_caller in &initial_analysis.fork_callers {
        println!("Fork caller : {:?}", fork_caller);
        let res = analyze_one_entry_point(&dwarf_dict, &mut dejavu_sets, fork_caller, &initial_analysis, &fun_ptrs_types_in_globals, &at_function_types, binary_path, sysfilter_path);
        println!("Syscalls len {}", res.syscalls.len());
        results.insert(fork_caller.clone(), res);
    }

    let mut file = File::create(output_path).expect("Failed to create output file");

    write!(file, "{{\n").unwrap();
    // Log info of no pruning

    write!(file, "\"No_Pruning\" : \n").unwrap();
    write!(file, "{{").unwrap();
    write!(file, "\"syscalls_len\" : {},\n", initial_analysis.syscalls.len()).unwrap();
    write!(file, "\"indirect_targets_len\" : {},\n", initial_analysis.indirect_targets_string.len()).unwrap();
    write!(file, "\"syscalls\" : {:?},\n", initial_analysis.syscalls).unwrap();
    write!(file, "\"indirect_targets\" : {:?}\n", initial_analysis.indirect_targets_string).unwrap();
    write!(file, "}}").unwrap();
    write!(file, ",\n").unwrap();

    // Rest of the log
    let mut i = 0;
    for (entry, res) in &results {
        let entry_point = format!("{}@{}", entry.name, entry.module);
        write!(file, "\"{}\" : \n", entry_point).unwrap();
        write!(file, "{{").unwrap();
        write!(file, "\"syscalls_len\" : {},\n", res.syscalls.len()).unwrap();
        write!(file, "\"indirect_targets_len\" : {},\n", res.indirect_targets.len()).unwrap();

        if initial_analysis.fork_callers.contains(&entry) {
            write!(file, "\"fork_caller\" : 1,\n").unwrap();
        }
        else if initial_analysis.thread_entry_points.contains(&entry) {
            write!(file, "\"thread_entry\" : 1,\n").unwrap();
        }

        write!(file, "\"syscalls\" : {:?},\n", res.syscalls).unwrap();
        write!(file, "\"indirect_targets\" : {:?}\n", res.indirect_targets).unwrap();
        write!(file, "}}").unwrap();
        if i != results.len() - 1 {
            write!(file, ",\n").unwrap();
        }
        i += 1;
    }
    write!(file, "\n}}").unwrap();
}

fn analyze_one_entry_point<'a, R: gimli::Reader<Offset = usize>>(
    dwarf_dict: &'a DwarfinfoDict<R>,
    dejavu_sets: &'a mut DejavuSets,
    entry: &Symbol,
    initial_analysis: &'a InitialAnalysis,
    fun_ptrs_types_in_globals: &'a HashSet<FunctionType>,
    at_function_types: &'a HashMap<Symbol, Option<FunctionType>>,
    binary_path: &str,
    sysfilter_path: &str) 
-> PrunedAnalysis {
    let authorized_ATs = do_pruning(dwarf_dict, dejavu_sets, entry, initial_analysis, 
                                    fun_ptrs_types_in_globals, at_function_types);

    let binary_name = binary_path.split('/').collect::<Vec<_>>();
    let authorized_fct_path = format!("{}_{}{}", binary_name.last().unwrap(), 
                                      entry.name, "_ATs.json");
    let output_path = format!("{}_{}{}", binary_name.last().unwrap(), entry.name, "_pruned.json");
    sysfilter::write_authorized_functions_json(&authorized_fct_path, &authorized_ATs);
    let pruned_results = sysfilter::pruned_sysfilter_analysis(sysfilter_path, binary_path, 
                                         &output_path, &authorized_fct_path);
    return pruned_results;
}


fn do_pruning<'a, R: gimli::Reader<Offset = usize>>(
    dwarf_dict: &'a DwarfinfoDict<R>,
    dejavu_sets: &'a mut DejavuSets,
    entry: &Symbol,
    initial_analysis: &'a InitialAnalysis,
    fun_ptrs_types_in_globals: &'a HashSet<FunctionType>,
    at_function_types: &'a HashMap<Symbol, Option<FunctionType>>) 
-> HashSet<Symbol>{

    // Get DCG
    let mut callgraph = sysfilter::get_DCG(&initial_analysis.direct_edges, entry);
    let mut current_authorized_ATs = HashSet::new();
    
    // If the entry point is __libc_start_main we explicitly add main as an authorized AT
    if entry.name == "__libc_start_main" {
        current_authorized_ATs.insert(
            Symbol {
                module: String::from("(executable)"),
                name: String::from("main"),
            });
        current_authorized_ATs.insert(
            Symbol {
                module: String::from("entrypoint"),
                name: String::from("main"),
            });
    }
    // Otherwise we explicitly remove it 
    else {
        current_authorized_ATs.remove(
            &Symbol {
                module: String::from("(executable)"),
                name: String::from("main"),
            });
        current_authorized_ATs.insert(
            Symbol {
                module: String::from("entrypoint"),
                name: String::from(&entry.name),
            });
    }

    let mut current_len = 0;
    let mut prev_len = 1;

    while current_len != prev_len {
        prev_len = current_len;
        let authorized_ATs = find_authorized_ATs(dwarf_dict, dejavu_sets, &callgraph, fun_ptrs_types_in_globals, &at_function_types);

        // Reset the callgraph to only consider the function that were just added
        callgraph = HashSet::new();

        let diff = authorized_ATs.difference(&current_authorized_ATs);

        //println!("Adding {} authorized ATs", diff.count());

        for fun in diff {
            callgraph.extend(sysfilter::get_DCG(&initial_analysis.direct_edges, fun));
        }

        current_authorized_ATs.extend(authorized_ATs);

        current_len = current_authorized_ATs.len();
        println!("current_len = {} prev_len = {}", current_len, prev_len);
    }

    // If main was added and the entry point is not __libc_start_main we remove it
    if !(entry.name == "__libc_start_main") {
        current_authorized_ATs.remove(
            &Symbol {
                module: String::from("(executable)"),
                name: String::from("main"),
            });
    }


    println!("initial : {} pruned : {}", at_function_types.len(), current_authorized_ATs.len());

    return current_authorized_ATs;
}

///
fn find_authorized_ATs<'a, R: gimli::Reader<Offset = usize>>(
    dwarf_dict: &'a DwarfinfoDict<R>,
    dejavu_sets: &'a mut DejavuSets,
    callgraph: &HashSet<Symbol>,
    fun_ptrs_types_in_globals: &'a HashSet<FunctionType>,
    at_function_types: &'a HashMap<Symbol, Option<FunctionType>>) 
-> HashSet<Symbol>{

    // DEBUG
    /*
    let sym = Symbol { module: String::from("libgnutls.so.30"), name: String::from("gnutls_x509_crl_init") };
    let mut syms = HashSet::new();
    syms.insert(sym);
    find_all_function_pointers_types(&dwarf_dict, dejavu_sets, &syms);
    panic!("Debug");
    */
    // /DEBU"G


    let all_fun_ptrs_types = find_all_function_pointers_types(&dwarf_dict,
                                                                  dejavu_sets,
                                                                  &callgraph);

    //println!("fun ptrs type set {:?}", all_fun_ptrs_types);

    let mut pruned_AT_set = HashSet::new();
    //let mut yes = 0;
    //let mut no = 0;
    for (fun, fun_type) in at_function_types {
        //println!("{:?}", fun_type);
        match fun_type {
            Some(fun_type) => { 
                if all_fun_ptrs_types.contains(&fun_type) 
                    || fun_ptrs_types_in_globals.contains(&fun_type) {
                    pruned_AT_set.insert(fun.clone());
                    //println!("YES");
                    //yes += 1;
                } else {
                    //println!("NO");
                    //no += 1;
                }
            }
            None => {
                pruned_AT_set.insert(fun.clone());
                //println!("YES {:?}", fun);
                //yes += 1;
            }
        }
    }
    //println!("yes : {} no: {}", yes, no);
    return pruned_AT_set;
}

fn find_relevant_CUs<R>(dwarfinfo_dict: &DwarfinfoDict<R>, 
                        initial_analysis: &InitialAnalysis) 
    -> ()  where R: Reader<Offset = usize>, <R as Reader>::Offset: LowerHex
{
    let mut relevant_CUs = HashMap::new();
    for module_name in dwarfinfo_dict.0.keys() {
        let mut CUs = HashSet::new();
        println!("{}", module_name);
        let dwarf = &dwarfinfo_dict.0[module_name];
        // Iterate over the compilation units.
        let mut iter = dwarf.units();
        while let Some(header) = iter.next().unwrap() {
            let unit = dwarf.unit(header).unwrap();
            // Iterate over the Debugging Information Entries (DIEs) in the unit.
            let mut depth = 0;
            let mut entries = unit.entries();
            while let Some((delta_depth, entry)) = entries.next_dfs().unwrap() {
                depth += delta_depth;
                if entry.tag() == gimli::constants::DW_TAG_subprogram && depth == 1 {
                    if let Some(name_value) = entry.attr_value(gimli::constants::DW_AT_name).unwrap() {
                        if let Some(curr_function_name) = decode_string(dwarf, &name_value) {
                            //println!("{}", curr_function_name);
                            let symbol = Symbol {
                                module: module_name.to_owned(),
                                name: curr_function_name,
                            };

                            if initial_analysis.callgraph.contains(&symbol) {
                                //println!("{:?}", symbol);
                                CUs.insert(symbol);
                            }
                        }
                    }
                }
            }
        }

        println!("{} {}", module_name, CUs.len());
        relevant_CUs.insert(module_name.to_string(), CUs);
    }
}

/// Return a VariableType from a type DIE 
fn type_DIE_to_type<R: gimli::Reader<Offset = usize>>(dwarf: &Dwarf<R>, 
                                      unit: &Unit<R>,
                                      entry: &DebuggingInformationEntry<R>)
    -> Result<VariableType, ()> where <R as Reader>::Offset: LowerHex {

    match entry.tag() {
        gimli::constants::DW_TAG_typedef 
        | gimli::constants::DW_TAG_base_type 
        | gimli::constants::DW_TAG_enumeration_type 
        | gimli::constants::DW_TAG_union_type
        | gimli::constants::DW_TAG_structure_type => {
            if let Some(at_name_value) = entry.attr_value(gimli::constants::DW_AT_name).unwrap() {
                let type_string = match decode_string(dwarf, &at_name_value) {
                    Some(s) => s,
                    None => {
                        // REMOVE THIS
                        // OR ADD SUPPORT FOR SUP FILE
                        /*
                        println!("{}, {:?}", entry.tag(), entry.offset());
                        let mut attrs = entry.attrs();
                        while let Some(attr) = attrs.next().unwrap() {println!("   {}: {:?}", attr.name(), attr.value());}
                        panic!();
                        */
                        return Err(());
                    },
                };
                return Ok(VariableType (vec![TypeToken::Name(type_string)]));
            }
        },
        // If this is a pointer, we find what it points to and return "POINTER to x"
        gimli::constants::DW_TAG_pointer_type => {
            match entry.attr_value(gimli::constants::DW_AT_type).unwrap() {
                // void*
                None => {return Ok(VariableType (vec![TypeToken::Pointer, TypeToken::Void]));}
                Some(at_type_value) => { 
                    //let pointed_type_DIE = get_DIE_at_offset(dwarf, unit, &at_type_value);
                    let (new_unit, off) = match unit_containing(dwarf, &at_type_value) {
                        Some((u, o)) => (u, o),
                        None => {return Err(());}
                    };
                    let mut pointed_type_type = if let Some(u) = new_unit {
                        let pointed_type_DIE = u.entry(UnitOffset(off))
                            .expect("Did not find entry at offset");
                        type_DIE_to_type(dwarf, &u, &pointed_type_DIE)?
                    } else {
                        let pointed_type_DIE = unit.entry(UnitOffset(off))
                            .expect("Did not find entry at offset");
                        type_DIE_to_type(dwarf, unit, &pointed_type_DIE)?
                    };
                    //let mut pointed_type_type = type_DIE_to_type(dwarf, unit, &pointed_type_DIE)?;
                    let mut variable_type = VariableType (vec![TypeToken::Pointer]);
                    variable_type.add_tokens(&mut pointed_type_type);
                    return Ok(variable_type);
                }
            }
        } 
        gimli::constants::DW_TAG_const_type => {
            match entry.attr_value(gimli::constants::DW_AT_type).unwrap() {
                // const void*
                None => {return Ok(VariableType (vec![TypeToken::Const, TypeToken::Void]));}
                Some(at_type_value) => { 
                    //let const_type_DIE = get_DIE_at_offset(dwarf, unit, &at_type_value);
                    let (new_unit, off) = unit_containing(dwarf, &at_type_value).unwrap();
                    let mut const_type_type = if let Some(u) = new_unit {
                        let const_type_DIE = u.entry(UnitOffset(off))
                            .expect("Did not find entry at offset");
                        type_DIE_to_type(dwarf, &u, &const_type_DIE)?
                    } else {
                        let const_type_DIE = unit.entry(UnitOffset(off))
                            .expect("Did not find entry at offset");
                        type_DIE_to_type(dwarf, unit, &const_type_DIE)?
                    };
                    //let mut const_type_type = type_DIE_to_type(dwarf, unit, &const_type_DIE)?;
                    let mut variable_type = VariableType (vec![TypeToken::Const]);
                    variable_type.add_tokens(&mut const_type_type);
                    return Ok(variable_type);
                }
            }
        } 
        gimli::constants::DW_TAG_subroutine_type => {
            let function_type = DIE_to_function_type(dwarf, unit, entry)?;
            return Ok(VariableType (vec![TypeToken::Function(function_type)]));
        }

        /*
        gimli::constants::DW_TAG_enumeration_type => {
            match entry.attr_value(gimli::constants::DW_AT_name).unwrap() {
                // void*
                None => {
                    panic!("Unnamed enum");
                }
                Some(at_name_value) => { 
                    let type_string = decode_string(dwarf, &at_name_value).unwrap();
                    return Ok(VariableType (vec![TypeToken::Name(type_string)]));

                    let pointed_type_DIE = get_DIE_at_offset(dwarf, unit, &at_type_value);
                    let mut pointed_type_type = type_DIE_to_type(dwarf, unit, &pointed_type_DIE)?;
                    let mut variable_type = VariableType (vec![TypeToken::Pointer]);
                    variable_type.add_tokens(&mut pointed_type_type);
                    return Ok(variable_type);
                }
            }
        } */

        // volatile and restrict are not strictly enforced by the compiler.
        // It is possible to call a function which takes a restrict pointer
        // with a non restrict pointer. Therefore we ignore those keyword and only
        // return the underlying type.
        gimli::constants::DW_TAG_restrict_type
        | gimli::constants::DW_TAG_volatile_type => {
            match entry.attr_value(gimli::constants::DW_AT_type).unwrap() {
                // restrict void*
                None => {return Ok(VariableType (vec![TypeToken::Void]));}
                Some(at_type_value) => { 
                    //let restricted_type_DIE = get_DIE_at_offset(dwarf, unit, &at_type_value);
                    //let mut restricted_type_type = type_DIE_to_type(dwarf, unit, &restricted_type_DIE)?;
                    let (new_unit, off) = unit_containing(dwarf, &at_type_value).unwrap();
                    let restricted_type_type = if let Some(u) = new_unit {
                        let restricted_type_DIE = u.entry(UnitOffset(off))
                            .expect("Did not find entry at offset");
                        type_DIE_to_type(dwarf, &u, &restricted_type_DIE)?
                    } else {
                        let restricted_type_DIE = unit.entry(UnitOffset(off))
                            .expect("Did not find entry at offset");
                        type_DIE_to_type(dwarf, unit, &restricted_type_DIE)?
                    };
                    return Ok(restricted_type_type);
                }
            }
        } 
        _ => { panic!("Unknown type DIE : {}", entry.tag()) },
    }
    Err(())
}

fn decode_string<R: gimli::Reader>(dwarf: &Dwarf<R>, 
                                   value: &gimli::AttributeValue<R>) 
-> Option<String> {
    match value {
        gimli::AttributeValue::DebugStrRef(offset) => {
            if let Ok(s) = dwarf.debug_str.get_str(*offset) {
                let string = s.to_string_lossy().unwrap().to_string();
                //println!("{}", string);
                Some(string)
            } else {
                panic!("Can't decode string");
            }
        },
        gimli::AttributeValue::DebugStrRefSup(offset) => {
            if let Some(s) = dwarf
                            .sup()
                            .and_then(|sup| sup.debug_str.get_str(*offset).ok()){
                let string = s.to_string_lossy().unwrap().to_string();
                println!("sup {}", string);
                Some(string)
            } else {
                None
            }
        }
        gimli::AttributeValue::String(s) => {
            let string = s.to_string_lossy().unwrap().to_string();
            //println!("{}", string);
            Some(string)
        }
        _ => {
            println!("{:?}", value);
            panic!("Can't decode string");
        }
    }

}

/// Return the unit containing the DIE at offset `off`
/// and the offset of the DIE in the unit
/// or None if no matching unit was found
fn unit_containing<R: gimli::Reader<Offset = usize>>(dwarf: &Dwarf<R>, 
                                     offset: &gimli::AttributeValue<R>) 
-> Option<(Option<Unit<R>>, usize)> {
    match offset { 
        gimli::AttributeValue::UnitRef(gimli::UnitOffset(off)) => {
            return Some((None, *off));
        }
        gimli::AttributeValue::DebugInfoRef(gimli::DebugInfoOffset(off)) => {
            let mut iter = dwarf.units();
            while let Some(header) = iter.next().unwrap() {
                //println!("unit offset : {:?}", header.offset());
                let cu_off = match header.offset() {
                    gimli::UnitSectionOffset::DebugInfoOffset(gimli::DebugInfoOffset(cu_offset)) => {
                        cu_offset
                    }
                    _ => {panic!("Could not handle offset");}
                };

                let unit = dwarf.unit(header).unwrap();
                let mut entries = unit.entries();
                while let Some((_delta_depth, entry)) = entries.next_dfs().unwrap() {
                    let entry_off = match entry.offset() {
                        gimli::UnitOffset(e) => e,
                        //_ => panic!("Could not handle entry offset {:?}", entry.offset())
                    };
                    /*
                    println!("{:x?}, ", entry.offset());
                    println!("{:x?} {:x?}", entry_off + cu_off, off);
                    */
                    if entry_off + cu_off == *off {
                        return Some((Some(unit), entry_off));
                    }
                }
            }
            None
        },
        _ => None
    }
}

/// Return a VariableType from a DIE that has a DW_AT_type attribute
fn DIE_to_type<R: gimli::Reader<Offset = usize>>(dwarf: &Dwarf<R>, 
                                 unit: &Unit<R>,
                                 entry: &DebuggingInformationEntry<R>)
-> Result<VariableType, ()> where <R as Reader>::Offset: LowerHex {

    // Find the DIE corresponding to the DW_AT_type attribute
    if let Some(at_type_value) = entry.attr_value(gimli::constants::DW_AT_type).unwrap() {
        //println!("{:?}", at_type_value);
        match at_type_value {
            gimli::AttributeValue::UnitRef(gimli::UnitOffset(off)) => {
                let type_die = unit.entry(UnitOffset(off)).expect("Did not find entry at offset");
                return type_DIE_to_type(dwarf, unit, &type_die);
            }
            // Could be replaced with unit_containing
            gimli::AttributeValue::DebugInfoRef(gimli::DebugInfoOffset(off)) => {
                //println!("{:?}", at_type_value);
                //
                // Could not find a better way in the gimli API to find a DIE
                // at a given debug_info offset. For now we iterate through the dwarf
                // and find the correct DIE. Should add this to gimli later.
                //
                let mut iter = dwarf.units();
                while let Some(header) = iter.next().unwrap() {
                    /*
                    match header.offset() {
                        gimli::UnitSectionOffset::DebugInfoOffset(gimli::DebugInfoOffset(cu_offset)) => {
                            if cu_offset < off {continue;}
                        }
                        _ => {panic!("Could not handle offset");}
                    }*/
                    let cu_off = match header.offset() {
                        gimli::UnitSectionOffset::DebugInfoOffset(gimli::DebugInfoOffset(cu_offset)) => {
                            cu_offset
                        }
                        _ => {panic!("Could not handle offset");}
                    };

                    let unit = dwarf.unit(header).unwrap();
                    // Iterate over the Debugging Information Entries (DIEs) in the unit.
                    let mut entries = unit.entries();
                    while let Some((_delta_depth, entry)) = entries.next_dfs().unwrap() {
                        let entry_off = match entry.offset() {
                            gimli::UnitOffset(e) => e,
                            //_ => panic!("Could not handle entry offset {:?}", entry.offset())
                        };
                        /*
                        println!("{:?}, ", entry.offset());
                        println!("{:?} {:?}", entry_off + cu_off, off);
                        */
                        if entry_off + cu_off == off {
                            return type_DIE_to_type(dwarf, &unit, entry);
                        }
                    }
                }
                return Err(());
                //panic!();
                //
                //
                //
            },
            _ => {
                //println!("{:?}", at_type_value);
                return Err(());
                //panic!("Unknown DW_AT_type value");
            }
        };
    }
    else {
        Err(())
    }
}

/// Get the function type from a DW_AT_subprogram DIE
fn DIE_to_function_type<R: gimli::Reader<Offset = usize>>(dwarf: &Dwarf<R>, 
                                          unit: &Unit<R>,
                                          entry: &DebuggingInformationEntry<R>)
-> Result<FunctionType, ()> where <R as Reader>::Offset: LowerHex {
    // Get a tree view rooted at this entry
    let mut tree = unit.entries_tree(Some(entry.offset())).unwrap();
    let root = tree.root().unwrap();

    //let attrs = root.entry().attrs();

    let return_type = DIE_to_type(dwarf, unit, root.entry())?;
    //println!("Return type : {:?}", return_type);

    /*
    println!("<{}><{:x}> {}", 1, root.entry().offset().0, root.entry().tag());
    while let Some(attr) = attrs.next().unwrap() {
        println!("   {}: {:?}", attr.name(), attr.value());
    }*/

    let mut arguments_types = vec!();
    let mut children = root.children();
    while let Some(child) = children.next().unwrap() {
        if child.entry().tag() == gimli::constants::DW_TAG_formal_parameter {
            let arg_type = DIE_to_type(dwarf, unit, child.entry())?;
            arguments_types.push(arg_type);
        }
    }

    //println!("{:?}", arguments_types);

    Ok(FunctionType {
        return_type,
        arguments_types,
    })
}

/// Find the function type of a function 
fn find_all_function_types<R>(dwarf: &Dwarf<R>, module_name: &str, indirect_targets: &HashSet<Symbol>) 
 -> HashMap<Symbol, Option<FunctionType>> where R: Reader<Offset = usize>, <R as Reader>::Offset: LowerHex {

    let mut all_function_types = HashMap::new();

    let mut iter = dwarf.units();
    while let Some(header) = iter.next().unwrap() {
        let unit = dwarf.unit(header).unwrap();
        let mut entries = unit.entries();
        while let Some((_delta_depth, entry)) = entries.next_dfs().unwrap() {
            if entry.tag() == gimli::constants::DW_TAG_subprogram {
                if let Some(name_value) = entry.attr_value(gimli::constants::DW_AT_name).unwrap() {
                    if let Some(curr_function_name) = decode_string(dwarf, &name_value) {
                        //println!("{}", curr_function_name);
                        let symbol = Symbol {
                            module: module_name.to_owned(),
                            name: curr_function_name,
                        };

                        if indirect_targets.contains(&symbol) {
                            //println!("{}", symbol.name);
                            let function_type = DIE_to_function_type(dwarf, &unit, entry);
                            //println!("{:?}", function_type);
                            match function_type {
                                Ok(t) => { all_function_types.insert(symbol, Some(t)); },
                                Err(_) => { all_function_types.insert(symbol, None); },
                            }
                        }
                    }
                }
            }
        }
    }

    for fun in indirect_targets {
        if fun.module == module_name {
            match all_function_types.get(fun) {
                Some(_) => (),
                None => {all_function_types.insert(fun.clone(), None);}
            }
        }
    }

    return all_function_types;
}

/*
/// Find the function type of a function 
fn find_function_type<R>(dwarf: &Dwarf<R>, function_name: &str) -> Result<FunctionType, ()> 
where R: Reader<Offset = usize>, <R as Reader>::Offset: LowerHex {
    println!("\nBBBBBBBBBBBBBBBBBBBBBBBBBB\n");
    // Iterate over the compilation units.
    let mut iter = dwarf.units();
    while let Some(header) = iter.next().unwrap() {
        /*
        println!(
            "Unit at <.debug_info+0x{:x}>",
            header.offset().as_debug_info_offset().unwrap().0
        );
        */
        let unit = dwarf.unit(header).unwrap();

        // Iterate over the Debugging Information Entries (DIEs) in the unit.
        let mut entries = unit.entries();
        while let Some((_delta_depth, entry)) = entries.next_dfs().unwrap() {
            if entry.tag() == gimli::constants::DW_TAG_subprogram {
                //println!("<{}><{:x}> {}", depth, entry.offset().0, entry.tag());
                // Should this be attr_value_raw?
                if let Some(name_value) = entry.attr_value(gimli::constants::DW_AT_name).unwrap() {
                    //println!("{:?}", name_value);
                    if let Some(curr_function_name) = match name_value {
                        gimli::AttributeValue::DebugStrRef(offset) => {
                            if let Ok(s) = dwarf.debug_str.get_str(offset) {
                                let curr_function_name = s.to_string_lossy().unwrap().to_string();
                                //println!("{}", curr_function_name);
                                Some(curr_function_name)
                            } else {
                                println!("<.debug_str+0x{:08x}>", offset.0);
                                None
                            }
                        },
                        gimli::AttributeValue::String(s) => {
                            let curr_function_name = s.to_string_lossy().unwrap().to_string();
                            //println!("{}", curr_function_name);
                            Some(curr_function_name)
                        }
                        _ => {panic!("Can't read name value");}
                    } {
                        //println!("{}", curr_function_name);
                        if curr_function_name == function_name {
                            return DIE_to_function_type(dwarf, &unit, entry);
                        }
                    }
                }
            }
        }
    }
    Err(())
}*/

fn find_function_pointers_in_type<R>(dwarf: &Dwarf<R>, unit: &Unit<R>, entry: &DebuggingInformationEntry<R>, dejavu: &mut HashSet<usize>) 
-> HashSet<FunctionType> where R: Reader<Offset = usize>, <R as Reader>::Offset: LowerHex {
    let entry_offset = entry.offset().to_debug_info_offset(&unit.header).unwrap().0;
    /*
    println!("Finding Function pointers in {} {:x?} {:x?} ", entry.tag(), entry.offset(),
    entry.offset().to_debug_info_offset(&unit.header).unwrap().0);
    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next().unwrap() {println!("   {}: {:?}", attr.name(), attr.value());} 
    */

    // If we already added the pointers of this type
    if dejavu.contains(&entry_offset){ 
        return HashSet::new(); 
    }

    dejavu.insert(entry_offset);
    //println!("{:?}", dejavu);

    match entry.tag() {
        // Type modifiers -> We look into the underlying type
        gimli::constants::DW_TAG_pointer_type
        | gimli::constants::DW_TAG_array_type
        | gimli::constants::DW_TAG_restrict_type
        | gimli::constants::DW_TAG_const_type
        | gimli::constants::DW_TAG_rvalue_reference_type
        | gimli::constants::DW_TAG_reference_type
        | gimli::constants::DW_TAG_atomic_type
        | gimli::constants::DW_TAG_volatile_type
        | gimli::constants::DW_TAG_typedef => {
            match entry.attr_value(gimli::constants::DW_AT_type).unwrap() {
                // void*
                None => {return HashSet::new();},
                Some(at_type_value) => { 
                    //let pointed_type_DIE = get_DIE_at_offset(dwarf, unit, &at_type_value);
                    let (new_unit, off) = match unit_containing(dwarf, &at_type_value) {
                        Some((u, o)) => (u, o),
                        None => {return HashSet::new();}
                    };
                    if let Some(u) = new_unit {
                        let pointed_type_DIE = u.entry(UnitOffset(off))
                            .expect("Did not find entry at offset");
                        return find_function_pointers_in_type(dwarf, &u, &pointed_type_DIE, dejavu);
                    } else {
                        let pointed_type_DIE = unit.entry(UnitOffset(off))
                            .expect("Did not find entry at offset");
                        return find_function_pointers_in_type(dwarf, unit, &pointed_type_DIE, dejavu);
                    }
                }
            }
        },
        gimli::constants::DW_TAG_subroutine_type => {
            let function_type = DIE_to_function_type(dwarf, unit, entry);
            //println!("AAAAAAAAAAAAA {:?}", function_type);
            match function_type {
                Ok(t) => { 
                    let mut set = HashSet::new();
                    set.insert(t); 
                    return set;
                }
                Err(_) => { return HashSet::new(); }
            };
        },
        gimli::constants::DW_TAG_structure_type 
        | gimli::constants::DW_TAG_class_type 
        | gimli::constants::DW_TAG_union_type => {
            let mut function_types = HashSet::new();
            let mut tree = unit.entries_tree(Some(entry.offset())).unwrap();
            let root = tree.root().unwrap();
            let mut children = root.children();
            // Iterate through members
            while let Some(child) = children.next().unwrap() {
                // Member functions
                if child.entry().tag() == gimli::constants::DW_TAG_subprogram {
                    continue;
                }

                // Nested classes
                if child.entry().tag() == gimli::constants::DW_TAG_class_type 
                    || child.entry().tag() == gimli::constants::DW_TAG_structure_type 
                    || child.entry().tag() == gimli::constants::DW_TAG_union_type {
                    function_types.extend(
                        find_function_pointers_in_type(dwarf, unit, &child.entry(), dejavu));
                    continue;
                }


                /* REMOVE */
                /*
                println!("Member: {} {:x?} {:x?} ", child.entry().tag(), child.entry().offset(), child.entry().offset().to_debug_info_offset(&unit.header).unwrap().0);
                let mut attrs = child.entry().attrs();
                while let Some(attr) = attrs.next().unwrap() {println!("   {}: {:?}", attr.name(), attr.value());} 
                */
                /* /REMOVE */


                let at_type_value;

                if child.entry().tag() == gimli::constants::DW_TAG_imported_declaration {
                    let at_import_value = child.entry().attr_value(gimli::constants::DW_AT_import)
                        .unwrap().expect("Imported declaration with no DW_AT_import");
                    let (new_unit, off) = match unit_containing(dwarf, &at_import_value) {
                        Some((u, o)) => (u, o),
                        None => {continue;}
                    };
                    let at_type_value_option = if let Some(u) = new_unit {
                        let member_imported_DIE = u.entry(UnitOffset(off))
                            .expect("Did not find entry at offset");
                        member_imported_DIE.attr_value(gimli::constants::DW_AT_type)
                            .unwrap()
                    } else {
                        let member_imported_DIE = unit.entry(UnitOffset(off))
                            .expect("Did not find entry at offset");
                        member_imported_DIE.attr_value(gimli::constants::DW_AT_type)
                            .unwrap()
                    };

                    at_type_value = match at_type_value_option {
                        Some(v) => v,
                        None => {
                            continue;
                            //panic!("This member has no type");
                        }
                    }
                }

                else if child.entry().tag() == gimli::constants::DW_TAG_GNU_template_parameter_pack
                  || child.entry().tag() == gimli::constants::DW_TAG_template_type_parameter {
                    continue;
                }

                else {
                    at_type_value = match child.entry().attr_value(gimli::constants::DW_AT_type)
                    .unwrap() {
                        Some(v) => v,
                        None => {
                            panic!("This member has no type");
                        }
                    }
                }

                //let member_type_DIE = get_DIE_at_offset(dwarf, unit, &at_type_value);
                let (new_unit, off) = match unit_containing(dwarf, &at_type_value) {
                    Some((u, o)) => (u, o),
                    None => {continue;}
                };
                let fct_ptrs = if let Some(u) = new_unit {
                    let member_type_DIE = u.entry(UnitOffset(off))
                        .expect("Did not find entry at offset");
                        find_function_pointers_in_type(dwarf, &u, &member_type_DIE, dejavu)
                } else {
                    let member_type_DIE = unit.entry(UnitOffset(off))
                        .expect("Did not find entry at offset");
                        find_function_pointers_in_type(dwarf, unit, &member_type_DIE, dejavu)
                };
                function_types.extend(fct_ptrs);
            }
            return function_types;
        }
        gimli::constants::DW_TAG_base_type
        | gimli::constants::DW_TAG_enumeration_type => {
            return HashSet::new();
        }
        _ => {panic!("Don't know how to find pointers in {}", entry.tag());}

    }
}

fn find_function_pointers_in_variable <R>(dwarf: &Dwarf<R>, 
                                          unit: &Unit<R>, 
                                          entry: &DebuggingInformationEntry<R>,
                                          dejavu: &mut HashSet<usize>) 
-> HashSet<FunctionType> where R: Reader<Offset = usize>, <R as Reader>::Offset: LowerHex {
    /*
    let entry_offset = entry.offset().to_debug_info_offset(&unit.header).unwrap().0;
    println!("Finding Function pointers in {} {:x?} {:x?} ", entry.tag(), entry.offset(),
    entry.offset().to_debug_info_offset(&unit.header).unwrap().0);
    */
    // Find the type of this entry
    let at_type_value = entry.attr_value(gimli::constants::DW_AT_type)
        .unwrap().expect("This variable has no type");
    //let pointed_type_DIE = get_DIE_at_offset(dwarf, unit, &at_type_value);
    let (new_unit, off) = match unit_containing(dwarf, &at_type_value) {
        Some((u, o)) => (u, o),
        None => {return HashSet::new();}
    };
    if let Some(u) = new_unit {
        let pointed_type_DIE = u.entry(UnitOffset(off))
            .expect("Did not find entry at offset");
        find_function_pointers_in_type(dwarf, &u, &pointed_type_DIE, dejavu)
    } else {
        let pointed_type_DIE = unit.entry(UnitOffset(off))
            .expect("Did not find entry at offset");
        find_function_pointers_in_type(dwarf, unit, &pointed_type_DIE, dejavu)
    }

}

fn find_function_pointers_in_callsite<R>(dwarf: &Dwarf<R>, 
                                         unit: &Unit<R>, 
                                         entry: &DebuggingInformationEntry<R>, 
                                         dejavu: &mut HashSet<usize>) 
-> HashSet<FunctionType> where R: Reader<Offset = usize>, <R as Reader>::Offset: LowerHex {
    // Finf the abstract origin (

    // Print DIE // DEBUG
    /*
    println!("{}", entry.tag());
    let mut attrs = entry.attrs();
    while let Some(attr) = attrs.next().unwrap() {println!("   {}: {:?}", attr.name(), attr.value());} */

    let abstract_origin = 
        if let Some(off) = entry.attr_value(gimli::constants::DW_AT_abstract_origin).unwrap(){
            off
        } 
        else if let Some(off) = entry.attr_value(gimli::constants::DW_AT_call_origin).unwrap(){
            off
        } 
        else if let Some(off) = entry.attr_value(gimli::constants::DW_AT_call_target).unwrap(){
            off
        } 
        else {
            //println!("Could not find this callsite's origin");
            return HashSet::new();
        };
    //let subprogram_DIE = get_DIE_at_offset(dwarf, unit, &abstract_origin);
    let (new_unit, off) = match unit_containing(dwarf, &abstract_origin) {
        Some((u, o)) => (u, o),
        None => {return HashSet::new();}
    };
    if let Some(u) = new_unit {
        let subprogram_DIE = u.entry(UnitOffset(off))
            .expect("Did not find entry at offset");
        // Find the return value
        match subprogram_DIE.attr_value(gimli::constants::DW_AT_type).unwrap() {
            // void*
            None => {
                return HashSet::new();
            }
            Some(at_type_value) => { 
                //let return_value_type_DIE = get_DIE_at_offset(dwarf, unit, &at_type_value);
                //return find_function_pointers_in_type(dwarf, unit, &return_value_type_DIE, dejavu);
                let (new_unit, off) = match unit_containing(dwarf, &at_type_value) {
                    Some((u2, o)) => (u2, o),
                    None => {return HashSet::new();}
                };
                if let Some(u2) = new_unit {
                    let return_value_type_DIE = u2.entry(UnitOffset(off))
                        .expect("New Unit. Did not find entry at offset");
                    find_function_pointers_in_type(dwarf, &u2, &return_value_type_DIE, dejavu)
                } else {
                    let return_value_type_DIE = u.entry(UnitOffset(off))
                        .expect("Did not find entry at offset");
                    find_function_pointers_in_type(dwarf, &u, &return_value_type_DIE, dejavu)
                }
            }
        }
    } else {
        let subprogram_DIE = unit.entry(UnitOffset(off))
            .expect("Did not find entry at offset");
        // Find the return value
        match subprogram_DIE.attr_value(gimli::constants::DW_AT_type).unwrap() {
            // void*
            None => {
                return HashSet::new();
            }
            Some(at_type_value) => { 
                //let return_value_type_DIE = get_DIE_at_offset(dwarf, unit, &at_type_value);
                //return find_function_pointers_in_type(dwarf, unit, &return_value_type_DIE, dejavu);
                let (new_unit, off) = match unit_containing(dwarf, &at_type_value) {
                    Some((u, o)) => (u, o),
                    None => {return HashSet::new();}
                };
                if let Some(u) = new_unit {
                    let return_value_type_DIE = u.entry(UnitOffset(off))
                        .expect("Did not find entry at offset");
                    find_function_pointers_in_type(dwarf, &u, &return_value_type_DIE, dejavu)
                } else {
                    let return_value_type_DIE = unit.entry(UnitOffset(off))
                        .expect("Did not find entry at offset");
                    find_function_pointers_in_type(dwarf, unit, &return_value_type_DIE, dejavu)
                }
            }
        }
    }


    /*
    // Find the return value
    match subprogram_DIE.attr_value(gimli::constants::DW_AT_type).unwrap() {
        // void*
        None => {
            return HashSet::new();
        }
        Some(at_type_value) => { 
            let return_value_type_DIE = get_DIE_at_offset(dwarf, unit, &at_type_value);
            return find_function_pointers_in_type(dwarf, unit, &return_value_type_DIE, dejavu);
        }
    }
    */
}

/// Find function pointers in a subprogram
/// entry is a DW_TAG_subprogram entry
fn find_function_pointers<R>(dwarf: &Dwarf<R>, unit: &Unit<R>, entry: &DebuggingInformationEntry<R>, dejavu: &mut HashSet<usize>)
-> HashSet<FunctionType> where R: Reader<Offset = usize>, <R as Reader>::Offset: LowerHex {

    let mut function_pointers_types: HashSet<FunctionType> = HashSet::new();
    let mut tree = unit.entries_tree(Some(entry.offset())).unwrap();
    let root = tree.root().unwrap();
    let mut children = root.children();
    while let Some(child) = children.next().unwrap() {
        //println!("Finding fptr in subprogram {} {:x?} {:x?}", child.entry().tag(), child.entry().offset(), child.entry().offset().to_debug_info_offset(&unit.header).unwrap().0);
        //println!("fptr_type : {:#?}", function_pointers_types);
        match child.entry().tag() {
            gimli::constants::DW_TAG_formal_parameter 
            | gimli::constants::DW_TAG_variable => {
                function_pointers_types.extend(
                    find_function_pointers_in_variable(dwarf, unit, child.entry(), dejavu));
            },
            gimli::constants::DW_TAG_GNU_call_site
            | gimli::constants::DW_TAG_inlined_subroutine => {
                function_pointers_types.extend(
                    find_function_pointers_in_callsite(dwarf, unit, child.entry(), dejavu));
            }
            // We deal with lexical block like a function
            gimli::constants::DW_TAG_lexical_block => {
                function_pointers_types.extend(
                    find_function_pointers(dwarf, unit, child.entry(), dejavu));
            }
            _ => ()

        }
    }
    function_pointers_types
}

/// Given a function name, find all the function pointer types present in that function
/// In local variables, parameters and function return value
fn find_all_function_pointers_types<R>(dwarfinfo_dict: &DwarfinfoDict<R>, 
                                       dejavu_sets: &mut DejavuSets,
                                       callgraph: &HashSet<Symbol>) 
-> HashSet<FunctionType> where R: Reader<Offset = usize>, <R as Reader>::Offset: LowerHex {

    let mut fct_ptrs_types = HashSet::new();

    for module_name in dwarfinfo_dict.0.keys() {
        let dwarf = &dwarfinfo_dict.0[module_name];
        let dejavu = dejavu_sets.0.get_mut(module_name).unwrap();
        // Iterate over the compilation units.
        let mut iter = dwarf.units();
        while let Some(header) = iter.next().unwrap() {
            let unit = dwarf.unit(header).unwrap();

            // Iterate over the Debugging Information Entries (DIEs) in the unit.
            let mut entries = unit.entries();
            // Maybe unnecessary to traverse in DFS
            // We can stay at depth 1
            while let Some((_delta_depth, entry)) = entries.next_dfs().unwrap() {
                if entry.tag() == gimli::constants::DW_TAG_subprogram {
                    // Should this be attr_value_raw?
                    if let Some(name_value) = entry.attr_value(gimli::constants::DW_AT_name).unwrap() {
                        if let Some(curr_function_name) = decode_string(dwarf, &name_value) {
                            let symbol = Symbol {
                                module: module_name.to_owned(),
                                name: curr_function_name,
                            };
                            if callgraph.contains(&symbol) {
                                fct_ptrs_types.extend(
                                    find_function_pointers(dwarf, &unit, entry, dejavu));
                            }
                        }
                    }
                }
            }
        }
    }

    fct_ptrs_types
}


/// Find function pointer types in global variables
fn find_function_pointer_types_in_globals<R>(dwarfinfo_dict: &DwarfinfoDict<R>, 
                                       dejavu_sets: &mut DejavuSets)
-> HashSet<FunctionType> where R: Reader<Offset = usize> + std::cmp::PartialEq, <R as Reader>::Offset: LowerHex {
    let mut fct_ptrs_types = HashSet::new();
    for module_name in dwarfinfo_dict.0.keys() {
        //println!("{}", module_name);
        let dwarf = &dwarfinfo_dict.0[module_name];
        let dejavu = dejavu_sets.0.get_mut(module_name).unwrap();
        // Iterate over the compilation units.
        let mut iter = dwarf.units();
        while let Some(header) = iter.next().unwrap() {
            let unit = dwarf.unit(header).unwrap();

            // Iterate over the Debugging Information Entries (DIEs) in the unit.
            let mut depth = 0;
            let mut entries = unit.entries();
            while let Some((delta_depth, entry)) = entries.next_dfs().unwrap() {
                depth += delta_depth;
                if entry.tag() == gimli::constants::DW_TAG_variable && depth == 1
                    // If it has the DW_AT_specification tag this is a non-defining declaration
                    && entry.attr_value(gimli::constants::DW_AT_specification).unwrap() == None
                    && entry.attr_value(gimli::constants::DW_AT_type).unwrap() != None {
                    //println!("<{}><{:x}> {}", depth, entry.offset().0 + cu_off, entry.tag());
                    fct_ptrs_types.extend(
                        find_function_pointers_in_variable(dwarf,
                                                          &unit,
                                                          entry,
                                                          dejavu));
                }
            }
        }
    }

    fct_ptrs_types
}
