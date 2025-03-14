run-server:
    cargo run --bin server

run-web:
    cd web && pnpm dev

test:
    cargo test --release