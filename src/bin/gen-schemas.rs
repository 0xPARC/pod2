use anyhow::Result;
use pod2::frontend::serialization::{MainPodHelper, SignedPodHelper};
use schemars::{gen::SchemaSettings, JsonSchema};

#[allow(dead_code)]
#[derive(JsonSchema)]
struct SchemaContainer {
    mainpod: MainPodHelper,
    signedpod: SignedPodHelper,
}

fn main() -> Result<()> {
    // Generate schemas using schemars
    let generator = SchemaSettings::draft2019_09().into_generator();
    let schema = generator.into_root_schema_for::<SchemaContainer>();

    // Serialize to a pretty JSON string
    let json_output = serde_json::to_string_pretty(&schema)?;

    // Print to stdout
    println!("{}", json_output);

    Ok(())
}
