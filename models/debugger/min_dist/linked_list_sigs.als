sig Date{}
sig Node {next: lone Node, hello: one next, dt: next  some -> one Date}

pred p[] {}
run p
