use pod2::middleware::{containers::Dictionary, StrKey, Value};

fn part_snapshot() -> Dictionary {
    Dictionary::new(
        [
            (StrKey::from("serial"), Value::from("ABC-123")),
            (StrKey::from("weight"), Value::from(10)),
        ]
        .into(),
    )
}

fn certificate(snapshot: &Dictionary) -> Dictionary {
    Dictionary::new([(StrKey::from("original"), Value::from(snapshot.clone()))].into())
}

fn assert_snapshot_is_readable(certificate: &Dictionary) {
    let stored_snapshot = certificate
        .get(&StrKey::from("original"))
        .unwrap()
        .expect("certificate contains its original snapshot");
    let snapshot = stored_snapshot
        .as_dictionary()
        .unwrap_or_else(|| panic!("expected a snapshot dictionary, got {stored_snapshot}"));
    assert_eq!(
        snapshot.get(&StrKey::from("weight")).unwrap(),
        Some(Value::from(10))
    );
}

#[test]
fn dictionary_remains_readable_beside_its_raw_commitment() {
    let snapshot = part_snapshot();
    let identifier = Value::from(snapshot.commitment());
    assert!(identifier.is_raw());
    assert_eq!(identifier.raw(), Value::from(snapshot.clone()).raw());

    let mut certificate = certificate(&snapshot);
    assert_snapshot_is_readable(&certificate);
    certificate
        .insert(&StrKey::from("part_id"), &identifier)
        .unwrap();
    assert!(certificate
        .get(&StrKey::from("part_id"))
        .unwrap()
        .unwrap()
        .is_raw());

    assert_snapshot_is_readable(&certificate);
}

#[test]
fn dictionary_remains_readable_when_sibling_parent_contains_its_raw_commitment() {
    let snapshot = part_snapshot();
    let certificate = certificate(&snapshot);
    let reference =
        Dictionary::new([(StrKey::from("part_id"), Value::from(snapshot.commitment()))].into());
    assert_snapshot_is_readable(&certificate);

    let bundle = Dictionary::new(
        [
            (
                StrKey::from("certificate"),
                Value::from(certificate.clone()),
            ),
            (StrKey::from("reference"), Value::from(reference)),
        ]
        .into(),
    );
    assert_snapshot_is_readable(&certificate);
    let bundled_certificate = bundle
        .get(&StrKey::from("certificate"))
        .unwrap()
        .unwrap()
        .as_dictionary()
        .unwrap();

    assert_snapshot_is_readable(&bundled_certificate);
}

#[test]
fn dictionary_remains_readable_when_clone_stores_its_raw_commitment() {
    let snapshot = part_snapshot();
    let certificate = certificate(&snapshot);
    let original_root = certificate.commitment();
    assert_snapshot_is_readable(&certificate);

    let mut copy = certificate.clone();
    copy.insert(
        &StrKey::from("part_id"),
        &Value::from(snapshot.commitment()),
    )
    .unwrap();
    assert_ne!(copy.commitment(), original_root);
    assert_eq!(certificate.commitment(), original_root);

    assert_snapshot_is_readable(&certificate);
}
