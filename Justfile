run-server:
    cargo run --bin server

run-web:
    cd web && pnpm dev

test:
    cargo test --release

test-web:
    cd web && pnpm test
