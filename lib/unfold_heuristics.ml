module Var = Soteria.Symex.Var

let vars_of_cvs (cvs : Core_value.t Iter.t) : Var.Hashset.t =
  Iter.flat_map Core_value.iter_vars cvs |> Iter.map fst |> Var.Hashset.of_iter

(** We define the following heuristics for deciding what to unfold:
    - Each matching in-parameter is worth 2 points
    - Each matching out-parameter is worth 1 point *)
let heuristics (relevant_values : Core_value.t Iter.t) :
    Core_value.t Predicates.unfold_heuristics =
 fun ins outs ->
  let relevant_vars = vars_of_cvs relevant_values in
  let ins_vars = vars_of_cvs (Iter.of_list ins) in
  let outs_vars = vars_of_cvs (Iter.of_list outs) in
  let ins_score = Var.Hashset.(cardinal @@ inter relevant_vars ins_vars) in
  let outs_score = Var.Hashset.(cardinal @@ inter relevant_vars outs_vars) in
  let score = (ins_score * 2) + outs_score in
  if score > 0 then Some score else None
