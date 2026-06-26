(lang dune 3.23)

(name soteria-cn)

(generate_opam_files true)

(source
 (github soteria-tools/soteria-cn))

(authors "Sacha-Élie Ayoun <sachaayoun@gmail.com>")

(maintainers "Sacha-Élie Ayoun <sachaayoun@gmail.com>")

(license Apache-2.0)

(documentation https://github.com/soteria-tools/soteria-cn)

(package
 (name soteria-cn)
 (synopsis "CN but based on Soteria")
 (description
  "This is a prototype for a version of the CN C verifier that is based on Soteria. It is not yet fully functional, but it is a work in progress.")
 (depends
  cn
  soteria
  soteria-c
  cerberus-lib
  fmt
  (ppx_mixins
   (= 0.2.0))
  ocaml)
 (tags
  (verification c soteria analysis "separation logic")))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
