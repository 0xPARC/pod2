# PODlang Playground

A browser-based playground for writing and validating PODlang predicates.

## Building

Install `wasm-pack` and build the WASM module:

```bash
npm install -g wasm-pack
wasm-pack build --target web --features wasm,backend_plonky2,mem_cache --no-default-features
```

## Running Locally

From the project root:

```bash
python3 -m http.server 8000
```

Then visit http://localhost:8000/playground/
