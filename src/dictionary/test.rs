use crate::dictionary::{Outline, Output, StenoDictionary};
use serde::{Deserialize, Serialize};

const DICT: &'static str = r#"
{
  "S": "is",
  "T": "it",
  "HEL/HROE": "hello"
}
"#;

#[test]
fn test_get() {
    let dict: StenoDictionary = serde_json::from_str(DICT).unwrap();
    dbg!(&dict);

    assert_eq!(
        dict.get(&Outline(vec!["S".to_string()])),
        Some(&Output::String("is".to_string()))
    );

    assert_eq!(
        dict.get(&Outline(vec!["T".to_string()])),
        Some(&Output::String("it".to_string()))
    );

    assert_eq!(dict.get(&Outline(vec!["non-existent".to_string()])), None);

    assert_eq!(
        dict.get(&Outline(vec!["HEL".to_string(), "HROE".to_string()])),
        Some(&Output::String("hello".to_string()))
    );

    assert_eq!(dict.get(&Outline(vec!["HEL/HROE".to_string()])), None);
}
