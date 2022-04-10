use std::fs;
use serde_json::Value;

pub fn load_json(path: &str) -> Value {
    let data = fs::read_to_string(path).expect("Failed to read json file");
    let json_data: Value = serde_json::from_str(&data).expect("Failed to decode json");
    return json_data["analysis_scope"].to_owned();
    return json_data;
}
