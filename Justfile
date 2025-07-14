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

# runs the executable
run *args:
    cargo run {{args}}

[private]
alias r := run

