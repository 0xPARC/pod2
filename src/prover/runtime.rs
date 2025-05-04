#[cfg(test)]
mod tests {
    use crate::lang::parse;

    #[test]
    fn test_runtime() {
        let input = r#"
REQUEST(
  ValueOf(?SELF_HOLDER_18Y["const_18y"], 1169909388)
  ValueOf(?SELF_HOLDER_1Y["const_1y"], 1706367566)
  Equal(?gov["socialSecurityNumber"], ?pay["socialSecurityNumber"])
  Lt(?gov["dateOfBirth"], ?SELF_HOLDER_18Y["const_18y"])
  Equal(?pay["startDate"], ?SELF_HOLDER_1Y["const_1y"])
  NotContains(?sanctions["sanctionsList"], ?gov["idNumber"])
)
    "#;
        let processed = parse(input).unwrap();
        println!("{:#?}", processed);
    }
}
