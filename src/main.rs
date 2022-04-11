//! A simple example of parsing `.debug_info`.

use core::fmt::LowerHex;
use object::{Object, ObjectSection};
use std::collections::{HashMap, HashSet};
use std::{borrow, env, fs};
use std::borrow::Cow;
use std::process::Command;

use gimli::{Dwarf, Reader, Unit, UnitOffset};
use gimli::DieReference::UnitRef;
use gimli::{DebuggingInformationEntry, EntriesCursor};
use gimli::EndianSlice;

use memmap::Mmap;

use sysfilter_pruning::sysfilter::{self, Symbol};

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
    ///
    Union,
    ///
    Pointer,
    Const,
    Enum,
    ///
    Void,
    Function(FunctionType)
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
    let output_json = format!("{}{}", binary_name.last().unwrap(), ".json");

    let initial_analysis = sysfilter::initial_sysfilter_analysis(
        sysfilter_path,
        binary_path,
        &output_json);
    println!("Initial analysis : {:#?}", initial_analysis);
    
    // Load the dwarf data in a really weird way to make to borrow checker happy
    // Mmap all the files in scope
    let mut mmap_dict: MmapDict = MmapDict (HashMap::new());
    for (module_name, scope_entry) in &initial_analysis.scope.0 {
        if !scope_entry.has_symbols {
            panic!("No symbols for {}", module_name);
        }
        println!("Loading dwarf of {}", module_name);
        let path = &scope_entry.path;

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

    // Find function types of indirect_targets
    let mut all_function_types = HashMap::new();
    for (module_name, _) in initial_analysis.scope.0 {
        println!("{:?}", module_name);
        let function_types = find_all_function_types(&dwarf_dict.0[&module_name], &module_name, &initial_analysis.indirect_targets);
        //println!("{:#?}", function_types);
        all_function_types.extend(function_types);
    }
    println!("{:#?}", all_function_types);

    // Get DCG
    

    /*
    let function_type = find_function_type(&dwarf_dict.0["libc.so.6"], "pthread_setschedparam");
    println!("{:?}", function_type);
    panic!();*/
    for fun in initial_analysis.indirect_targets {
        println!("{:?}", fun);
        let function_type = find_function_type(&dwarf_dict.0[&fun.module], &fun.name);
        println!("{:?}", function_type);
    }
    panic!();

    find_function_pointers_types(&dwarf_dict.0["(executable)"], "main");
    let function_type = find_function_type(&dwarf_dict.0["(executable)"], "main");
}

/// Returns the DIE at the offset represented by the attribute value off
fn get_DIE_at_offset<'a, R: gimli::Reader>(dwarf: &'a gimli::Dwarf<R>, unit: &'a Unit<R>, offset: &gimli::AttributeValue<R>) 
-> DebuggingInformationEntry<'a, 'a, R> {
    match offset {
        gimli::AttributeValue::UnitRef(UnitOffset(off)) => {
            { return unit.entry(UnitOffset(*off)).expect("Did not find entry at offset"); }
        }
        _ => {
            panic!("Invalid offset {:?}", offset);
        }
    };
}

/// Return a VariableType from a type DIE 
fn type_DIE_to_type<R: gimli::Reader>(dwarf: &Dwarf<R>, 
                                      unit: &Unit<R>,
                                      entry: &DebuggingInformationEntry<R>)
    -> Result<VariableType, ()> where <R as Reader>::Offset: LowerHex {

    match entry.tag() {
        gimli::constants::DW_TAG_typedef 
        | gimli::constants::DW_TAG_base_type 
        | gimli::constants::DW_TAG_enumeration_type 
        | gimli::constants::DW_TAG_structure_type => {
            if let Some(at_name_value) = entry.attr_value(gimli::constants::DW_AT_name).unwrap() {
                let type_string = decode_string(dwarf, &at_name_value).unwrap();
                return Ok(VariableType (vec![TypeToken::Name(type_string)]));
            }
        },
        // If this is a pointer, we find what it points to and return "POINTER to x"
        gimli::constants::DW_TAG_pointer_type => {
            match entry.attr_value(gimli::constants::DW_AT_type).unwrap() {
                // void*
                None => {return Ok(VariableType (vec![TypeToken::Pointer, TypeToken::Void]));}
                Some(at_type_value) => { 
                    let pointed_type_DIE = get_DIE_at_offset(dwarf, unit, &at_type_value);
                    let mut pointed_type_type = type_DIE_to_type(dwarf, unit, &pointed_type_DIE)?;
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
                    let const_type_DIE = get_DIE_at_offset(dwarf, unit, &at_type_value);
                    let mut const_type_type = type_DIE_to_type(dwarf, unit, &const_type_DIE)?;
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

        gimli::constants::DW_TAG_restrict_type => {
            match entry.attr_value(gimli::constants::DW_AT_type).unwrap() {
                // restrict void*
                None => {return Ok(VariableType (vec![TypeToken::Void]));}
                Some(at_type_value) => { 
                    let restricted_type_DIE = get_DIE_at_offset(dwarf, unit, &at_type_value);
                    let mut restricted_type_type = type_DIE_to_type(dwarf, unit, &restricted_type_DIE)?;
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
        gimli::AttributeValue::String(s) => {
            let string = s.to_string_lossy().unwrap().to_string();
            //println!("{}", string);
            Some(string)
        }
        _ => {panic!("Can't decode string");}
    }

}

/// Return a VariableType from a DIE that has a DW_AT_type attribute
fn DIE_to_type<R: gimli::Reader>(dwarf: &Dwarf<R>, 
                                 unit: &Unit<R>,
                                 entry: &DebuggingInformationEntry<R>)
-> Result<VariableType, ()> where <R as Reader>::Offset: LowerHex {

    // Find the DIE corresponding to the DW_AT_type attribute
    if let Some(at_type_value) = entry.attr_value(gimli::constants::DW_AT_type).unwrap() {
        //println!("{:?}", at_type_value);
        let type_DIE = match at_type_value {
            gimli::AttributeValue::UnitRef(UnitOffset(off)) => {
                unit.entry(UnitOffset(off)).expect("Did not find entry at offset")
            }
            _ => {
                panic!("Unknown DW_AT_type value");
            }
        };
        //println!("Found type DIE {}", type_DIE.tag());
        let variable_type = type_DIE_to_type(dwarf, unit, &type_DIE);
        //println!("{:?}", variable_type);
        return variable_type;
    }
    else {
        Err(())
    }
}

/// Get the function type from a DW_AT_subprogram DIE
fn DIE_to_function_type<R: gimli::Reader>(dwarf: &Dwarf<R>, 
                                          unit: &Unit<R>,
                                          entry: &DebuggingInformationEntry<R>)
-> Result<FunctionType, ()> where <R as Reader>::Offset: LowerHex {
    // Get a tree view rooted at this entry
    let mut tree = unit.entries_tree(Some(entry.offset())).unwrap();
    let root = tree.root().unwrap();

    let mut attrs = root.entry().attrs();

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

    println!("{:?}", arguments_types);

    Ok(FunctionType {
        return_type,
        arguments_types,
    })
}

/// Find the function type of a function 
fn find_all_function_types<R>(dwarf: &Dwarf<R>, module_name: &str, indirect_targets: &Vec<Symbol>) 
 -> HashMap<Symbol, FunctionType> where R: Reader, <R as Reader>::Offset: LowerHex {

    let mut all_function_types = HashMap::new();

    let mut iter = dwarf.units();
    while let Some(header) = iter.next().unwrap() {
        let unit = dwarf.unit(header).unwrap();
        let mut depth = 0;
        let mut entries = unit.entries();
        while let Some((delta_depth, entry)) = entries.next_dfs().unwrap() {
            depth += delta_depth;
            if entry.tag() == gimli::constants::DW_TAG_subprogram {
                if let Some(name_value) = entry.attr_value(gimli::constants::DW_AT_name).unwrap() {
                    if let Some(curr_function_name) = decode_string(dwarf, &name_value) {
                        //println!("{}", curr_function_name);
                        let symbol = Symbol {
                            module: module_name.to_owned(),
                            name: curr_function_name,
                        };

                        if indirect_targets.contains(&symbol) {
                            println!("{}", symbol.name);
                            println!("BLABLABLA");
                            let function_type = DIE_to_function_type(dwarf, &unit, entry);
                            println!("{:?}", function_type);
                            match function_type {
                                Ok(t) => { all_function_types.insert(symbol, t); },
                                Err(_) => (),
                            }
                        }
                    }
                }
            }
        }
    }
    return all_function_types;
}

/// Find the function type of a function 
fn find_function_type<R>(dwarf: &Dwarf<R>, function_name: &str) -> Result<FunctionType, ()> 
where R: Reader, <R as Reader>::Offset: LowerHex {
    println!("\nAZERAZERAZERAZERAZERAZERAZERAZERAZERAZERAZER\n");
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
        let mut depth = 0;
        let mut entries = unit.entries();
        while let Some((delta_depth, entry)) = entries.next_dfs().unwrap() {
            depth += delta_depth;
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
}

fn find_function_pointers_in_type<R>(dwarf: &Dwarf<R>, unit: &Unit<R>, entry: &DebuggingInformationEntry<R>) 
-> HashSet<FunctionType> where R: Reader, <R as Reader>::Offset: LowerHex {
    match entry.tag() {
        gimli::constants::DW_TAG_pointer_type
        | gimli::constants::DW_TAG_array_type
        | gimli::constants::DW_TAG_typedef => {
            match entry.attr_value(gimli::constants::DW_AT_type).unwrap() {
                // void*
                None => {return HashSet::new();},
                Some(at_type_value) => { 
                    let pointed_type_DIE = get_DIE_at_offset(dwarf, unit, &at_type_value);
                    return find_function_pointers_in_type(dwarf, unit, &pointed_type_DIE);
                }
            }
        },
        gimli::constants::DW_TAG_subroutine_type => {
            let function_type = DIE_to_function_type(dwarf, unit, entry);
            println!("AAAAAAAAAAAAA {:?}", function_type);
            return match function_type {
                Ok(t) => { 
                    let mut set = HashSet::new();
                    set.insert(t); 
                    return set;
                }
                Err(_) => { return HashSet::new(); }
            };
        },
        gimli::constants::DW_TAG_structure_type => {
            let mut function_types = HashSet::new();
            let mut tree = unit.entries_tree(Some(entry.offset())).unwrap();
            let root = tree.root().unwrap();
            let mut attrs = root.entry().attrs();
            let mut children = root.children();
            // Iterate through members
            while let Some(child) = children.next().unwrap() {
                println!("{}", child.entry().tag());
                let at_type_value = child.entry().attr_value(gimli::constants::DW_AT_type)
                    .unwrap().expect("This local var or parameter has no type");
                let member_type_DIE = get_DIE_at_offset(dwarf, unit, &at_type_value);
                function_types.extend(
                    find_function_pointers_in_type(dwarf, unit, &member_type_DIE));

            }
            return function_types;
        }
        gimli::constants::DW_TAG_base_type => {
            return HashSet::new();
        }
        _ => {panic!("Don't know how to find pointers in {}", entry.tag());}

    }
}

fn find_function_pointers_in_variable <R>(dwarf: &Dwarf<R>, 
                                          unit: &Unit<R>, 
                                          entry: &DebuggingInformationEntry<R>) 
-> HashSet<FunctionType> where R: Reader, <R as Reader>::Offset: LowerHex {
    // Find the type of this entry
    let at_type_value = entry.attr_value(gimli::constants::DW_AT_type)
        .unwrap().expect("This local var or parameter has no type");
    let pointed_type_DIE = get_DIE_at_offset(dwarf, unit, &at_type_value);

    find_function_pointers_in_type(dwarf, unit, &pointed_type_DIE)
}

fn find_function_pointers_in_callsite<R>(dwarf: &Dwarf<R>, unit: &Unit<R>, entry: &DebuggingInformationEntry<R>) 
-> HashSet<FunctionType> where R: Reader, <R as Reader>::Offset: LowerHex {
    // Finf the abstract origin (
    let abstract_origin = entry.attr_value(gimli::constants::DW_AT_abstract_origin)
        .unwrap().expect("This local var or parameter has no type");
    let subprogram_DIE = get_DIE_at_offset(dwarf, unit, &abstract_origin);


    // Find the return value
    match subprogram_DIE.attr_value(gimli::constants::DW_AT_type).unwrap() {
        // void*
        None => {
            return HashSet::new();
        }
        Some(at_type_value) => { 
            println!("This function returns something!");
            let return_value_type_DIE = get_DIE_at_offset(dwarf, unit, &at_type_value);
            return find_function_pointers_in_type(dwarf, unit, &return_value_type_DIE);
        }
    }
}

/// Find function pointers in a subprogram
/// entry is a DW_TAG_subprogram entry
fn find_function_pointers<R>(dwarf: &Dwarf<R>, unit: &Unit<R>, entry: &DebuggingInformationEntry<R>)
-> Result<HashSet<FunctionType>, ()> where R: Reader, <R as Reader>::Offset: LowerHex {

    let mut function_pointers_types: HashSet<FunctionType> = HashSet::new();

    let mut tree = unit.entries_tree(Some(entry.offset())).unwrap();
    let root = tree.root().unwrap();
    let mut attrs = root.entry().attrs();
    let mut children = root.children();
    while let Some(child) = children.next().unwrap() {
        println!("Finding fptr in {}", child.entry().tag());
        println!("fptr_type : {:#?}", function_pointers_types);
        match child.entry().tag() {
            gimli::constants::DW_TAG_formal_parameter 
            | gimli::constants::DW_TAG_variable => {
                function_pointers_types.extend(
                    find_function_pointers_in_variable(dwarf, unit, child.entry()));
            },
            gimli::constants::DW_TAG_GNU_call_site
            | gimli::constants::DW_TAG_inlined_subroutine => {
                function_pointers_types.extend(
                    find_function_pointers_in_callsite(dwarf, unit, child.entry()));
            }
            // We deal with lexical block like a function
            gimli::constants::DW_TAG_lexical_block => {
                return find_function_pointers(dwarf, unit, child.entry());
            }
            _ => ()

        }
    }
    Err(())
}

/// Given a function name, find all the function pointer types present in that function
/// In local variables, parameters and function return value
fn find_function_pointers_types<R>(dwarf: &Dwarf<R>, function_name: &str) 
-> Result<HashSet<FunctionType>, ()> where R: Reader, <R as Reader>::Offset: LowerHex {
    // Iterate over the compilation units.
    let mut iter = dwarf.units();
    while let Some(header) = iter.next().unwrap() {
        let unit = dwarf.unit(header).unwrap();

        // Iterate over the Debugging Information Entries (DIEs) in the unit.
        let mut depth = 0;
        let mut entries = unit.entries();
        while let Some((delta_depth, entry)) = entries.next_dfs().unwrap() {
            depth += delta_depth;
            if entry.tag() == gimli::constants::DW_TAG_subprogram {
                // Should this be attr_value_raw?
                if let Some(name_value) = entry.attr_value(gimli::constants::DW_AT_name).unwrap() {
                    //println!("{:?}", name_value);
                    if let Some(curr_function_name) = match name_value {
                        gimli::AttributeValue::DebugStrRef(offset) => {
                            if let Ok(s) = dwarf.debug_str.get_str(offset) {
                                let curr_function_name = s.to_string_lossy().unwrap().to_string();
                                Some(curr_function_name)
                            } else {
                                None
                            }
                        },
                        gimli::AttributeValue::String(s) => {
                            let curr_function_name = s.to_string_lossy().unwrap().to_string();
                            Some(curr_function_name)
                        }
                        _ => {panic!("Can't read name value");}
                    } {
                        if curr_function_name == function_name {
                            return find_function_pointers(dwarf, &unit, entry);
                        }
                    }
                }
            }
        }
    }
    Err(())
}

fn dump_file(object: &object::File, endian: gimli::RunTimeEndian) -> Result<(), gimli::Error> {
    // Load a section and return as `Cow<[u8]>`.
    let load_section = |id: gimli::SectionId| -> Result<borrow::Cow<[u8]>, gimli::Error> {
        match object.section_by_name(id.name()) {
            Some(ref section) => Ok(section
                .uncompressed_data()
                .unwrap_or(borrow::Cow::Borrowed(&[][..]))),
            None => Ok(borrow::Cow::Borrowed(&[][..])),
        }
    };

    // Load all of the sections.
    let dwarf_cow = gimli::Dwarf::load(&load_section)?;

    // Borrow a `Cow<[u8]>` to create an `EndianSlice`.
    let borrow_section: &dyn for<'a> Fn(
        &'a borrow::Cow<[u8]>,
    ) -> gimli::EndianSlice<'a, gimli::RunTimeEndian> =
        &|section| gimli::EndianSlice::new(&*section, endian);

    // Create `EndianSlice`s for all of the sections.
    let dwarf = dwarf_cow.borrow(&borrow_section);

    // Iterate over the compilation units.
    let mut iter = dwarf.units();
    while let Some(header) = iter.next()? {
        /*
        println!(
            "Unit at <.debug_info+0x{:x}>",
            header.offset().as_debug_info_offset().unwrap().0
        );*/
        let unit = dwarf.unit(header)?;

        // Iterate over the Debugging Information Entries (DIEs) in the unit.
        let mut depth = 0;
        let mut entries = unit.entries();
        while let Some((delta_depth, entry)) = entries.next_dfs()? {
            depth += delta_depth;
            //println!("<{}><{:x}> {}", depth, entry.offset().0, entry.tag());

            // Iterate over the attributes in the DIE.
            let mut attrs = entry.attrs();
            while let Some(attr) = attrs.next()? {
                println!("   {}: {:?}", attr.name(), attr.value());
                match attr.value() {
                    gimli::AttributeValue::DebugStrOffsetsBase(base) => {
                        panic!("BLI");
                    }
                    gimli::AttributeValue::DebugStrOffsetsIndex(index) => {
                        panic!("BLA");
                    }
                    gimli::AttributeValue::DebugStrRef(offset) => {
                        println!("BLO");
						if let Ok(s) = dwarf.debug_str.get_str(offset) {
							println!("{}", s.to_string_lossy());
						} else {
							println!("<.debug_str+0x{:08x}>", offset.0);
						}
                    }
                    _ => (),
                }
            }
        }
    }
    Ok(())
}
