# Just a task runner
# <https://github.com/casey/just>

# shows this help message
help:
    @just -l

# builds the library
build *args:
    cargo build {{args}}

[private]
alias b := build

# builds the documentation
doc *args:
    cargo doc {{args}} # -- open

[private]
alias d := doc

# runs the documentation test
doctest *args:
    cargo test --doc {{args}} # -- open

[private]
alias dt := doctest

# runs the tests
test *args:
    cargo test {{args}} # -- open

[private]
alias t := test

# runs the executable
run *args:
    cargo run {{args}}

[private]
alias r := run

# watches change and runs `cargo doc`. requires `cargo-watch`.
watch *args:
    cargo watch -x doc {{args}}

[private]
alias w := watch

