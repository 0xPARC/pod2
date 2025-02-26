# POD2

## Usage
- Run tests: `cargo test --release`
- Rustfmt: `cargo fmt`
- Check [typos](https://github.com/crate-ci/typos): `typos -c .github/workflows/typos.toml`

## Book
The `book` contains the specification of POD2. A rendered version of the site can be found at: https://0xparc.github.io/pod2/

To run it locally:
- Requirements
	- [mdbook](https://github.com/rust-lang/mdBook): `cargo install mdbook`
	- [mdbook-katex](https://github.com/lzanini/mdbook-katex): `cargo install mdbook-katex`
- Go to the book directory: `cd book`
- Run the mdbook: `mdbook serve`
