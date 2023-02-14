(lang dune 3.5)

(name ivec)

(generate_opam_files true)

(source
 (github plankp/ivec))

(authors "Paul Teng")

(maintainers "plankp@outlook.com")

(documentation https://github.com/plankp/ivec/blob/main/README.md)

(package
 (name ivec)
 (synopsis "Immutable Array programming")
 (depends ocaml dune zarith menhir))

(using menhir 2.1)
