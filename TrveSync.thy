theory TrveSync
imports Main
begin

datatype expr =
  Doc
| Var string
| Get expr string
| Iter expr
| Next expr

datatype id =
  Root
| Head
| Id nat nat
| Key string

datatype state_key =
  MapT  id
| ListT id
| RegT  id

datatype primitive =
  Null
| Str string
| Int int
| Bool bool

datatype doc_state =
  Prim primitive
| IdRef id
| Ctx "(state_key * id set * doc_state) list"

datatype cursor = Cursor "state_key list" id

datatype state =
  State doc_state "string \<Rightarrow> cursor option"

fun defined_var :: "string \<Rightarrow> state \<Rightarrow> bool" where
"defined_var x (State _ vars) = (x \<in> dom vars)"

fun let_var :: "state \<Rightarrow> string \<Rightarrow> cursor \<Rightarrow> state" where
"let_var (State doc vars) key val = State doc (vars(key \<mapsto> val))"

fun get_id :: "state_key \<Rightarrow> id" where
  "get_id (MapT  x) = x"
| "get_id (ListT x) = x"
| "get_id (RegT  x) = x"

fun get_first_diff :: "(state_key * id set * doc_state) list \<Rightarrow> id \<Rightarrow> id option" where
  "get_first_diff ((key, pres, _) # rest) prev_id = (
    if (get_id key) = prev_id \<or> pres = {}
    then get_first_diff rest prev_id
    else Some (get_id key)
  )"
| "get_first_diff [] _ = None"

fun get_next :: "doc_state \<Rightarrow> cursor \<Rightarrow> cursor option" where
  "get_next (Ctx ((key, pres, child) # rest)) (Cursor [] prev_id) = (
    if (get_id key) \<noteq> prev_id
    then get_next (Ctx rest) (Cursor [] prev_id)
    else (
      case get_first_diff rest prev_id of
        Some(next_id) \<Rightarrow> Some (Cursor [] next_id)
      | None \<Rightarrow> None
    )
  )"
| "get_next (Ctx ((key, pres, child) # rest)) (Cursor (k#ks) kn) = (
    if key \<noteq> k
    then get_next (Ctx rest) (Cursor (k#ks) kn)
    else (
      case get_next child (Cursor ks kn) of
        Some (Cursor ks1 kn1) \<Rightarrow> Some (Cursor (k#ks1) kn1)
      | None \<Rightarrow> None
    )
  )" |
"get_next _ _ = None"

fun eval_cur :: "state \<Rightarrow> expr \<Rightarrow> cursor option" where
  "eval_cur _ Doc = Some (Cursor [] Root)"
| "eval_cur (State doc vars) (Var x) = vars x"
| "eval_cur state (Get expr key) = (
    case eval_cur state expr of
      Some (Cursor ks kn) \<Rightarrow> Some (Cursor (ks @ [MapT kn]) (Key key))
    | None \<Rightarrow> None
  )"
| "eval_cur state (Iter expr) = (
    case eval_cur state expr of
      Some (Cursor ks kn) \<Rightarrow> Some (Cursor (ks @ [ListT kn]) Head)
    | None \<Rightarrow> None
  )"
| "eval_cur (State doc vars) (Next expr) = (
    case eval_cur (State doc vars) expr of
      Some cursor \<Rightarrow> get_next doc cursor
    | None \<Rightarrow> None
  )"

inductive valid_expr :: "state \<Rightarrow> expr \<Rightarrow> bool" for state where
expr_doc:  "valid_expr state Doc" |
expr_var:  "defined_var x state \<Longrightarrow> valid_expr state (Var x)" |
expr_get:  "valid_expr state expr \<Longrightarrow> valid_expr state (Get expr key)" |
expr_iter: "valid_expr state expr \<Longrightarrow> valid_expr state (Iter expr)" |
expr_next: "valid_expr state expr \<Longrightarrow> valid_next state expr \<Longrightarrow> valid_expr state (Next expr)"

definition empty_state :: state
where "empty_state = State (Ctx []) Map.empty"

lemma "valid_expr empty_state Doc"
by (rule expr_doc)

lemma "valid_expr (let_var empty_state ''hi'' (Cursor [] Root)) (Var ''hi'')"
by (simp, rule expr_var, rule expr_doc)

lemma "valid_expr empty_state (Get Doc ''hi'')"
by (rule expr_get, rule expr_doc)

lemma "valid_expr empty_state (Iter Doc)"
by (rule expr_iter, rule expr_doc)

end
