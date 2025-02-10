cargo run --release -- -s -t 5min $1 --vsids-only --restart 1
cargo run --release -- -s -t 5min $1 --forward-explanation --vsids-only --restart 1
cargo run --release -- -s -t 5min $1 --forward-explanation --forward-limit 3 --vsids-only --restart 1
cargo run --release -- -s -t 5min $1 --forward-explanation --forward-limit 5 --vsids-only --restart 1
cargo run --release -- -s -t 5min $1 --forward-explanation --forward-limit 1000 --vsids-only --restart 1
