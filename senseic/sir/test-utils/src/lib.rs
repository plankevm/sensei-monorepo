pub fn assert_trim_strings_eq_with_diff(actual: &str, expected: &str, context_name: &str) {
    let actual = actual.trim();
    let expected = expected.trim();

    if actual == expected {
        return;
    }

    eprintln!("=== {context_name} mismatch ===");
    pretty_assertions::assert_str_eq!(expected, actual);
}
