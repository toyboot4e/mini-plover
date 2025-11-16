use crate::plover_stroke::{KeySide, LetterWithSide, StenoSystem};

fn parse_keys(s: &str) -> Option<Vec<LetterWithSide>> {
    s.split_whitespace()
        .map(LetterWithSide::parse)
        .collect::<Option<Vec<_>>>()
}

fn english_system_keys() -> Vec<LetterWithSide> {
    let s = r##"
        #
        S- T- K- P- W- H- R-
        A- O-
        *
        -E -U
        -F -R -P -B -L -G -T -S -D -Z
"##;

    parse_keys(s).unwrap()
}

fn english_system() -> StenoSystem {
    StenoSystem::new(&english_system_keys(), &['A', 'O', '*', 'E', 'U']).unwrap()
}

#[test]
fn test_minimal() {
    let system = english_system();
    assert_eq!(
        system.right_keys_index,
        english_system_keys()
            .iter()
            .position(|l| *l
                == LetterWithSide {
                    letter: 'E',
                    side: KeySide::Right
                })
            .unwrap(),
    );
}
