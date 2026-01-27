# PODlang Playground

A web-based playground for writing and validating PODlang predicates in your browser.

## Building

1. Install `wasm-pack`:
```bash
curl https://rustwasm.github.io/wasm-pack/installer/init.sh -sSf | sh
```

2. Build the WASM module:
```bash
wasm-pack build --target web --features wasm --no-default-features
```

This will generate the WASM module in `pkg/`.

## Running

Serve the playground directory with any static file server:

```bash
python3 -m http.server 8000
```

Then open http://localhost:8000/playground/ in your browser.

Alternatively, use other servers:
```bash
npx serve playground
```

## Features

- Live PODlang parser validation
- Syntax highlighting via Monaco-style interface
- Example predicates included
- Shows parsed predicate names on success
- Detailed error messages on parse failure
