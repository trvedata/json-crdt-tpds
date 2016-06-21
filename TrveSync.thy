theory TrveSync
imports Main
begin

datatype expr =
  Doc |
  Var string |
  Get expr string |
  Iter expr |
  Next expr

datatype id =
  Root |
  Head |
  Tail |
  Id nat nat |
  Key string

datatype state_key =
  MapT  id |
  ListT id |
  RegT  id |
  NextT id |
  Pres  id

datatype primitive =
  Null       |
  Str string |
  Int int    |
  Bool bool

datatype doc_state =
  Prim primitive |
  IdRef id |
  Ctx "state_key \<Rightarrow> doc_state option"

datatype cursor = Cursor "state_key list" id

datatype state =
  State doc_state "string \<Rightarrow> cursor option"

fun defined_var :: "string \<Rightarrow> state \<Rightarrow> bool" where
"defined_var x (State _ vars) = (x \<in> dom vars)"

fun let_var :: "state \<Rightarrow> string \<Rightarrow> cursor \<Rightarrow> state" where
"let_var (State doc vars) key val = (State doc (vars(key \<mapsto> val)))"

inductive valid_cur :: "doc_state \<Rightarrow> cursor \<Rightarrow> bool" where
cur1: "valid_cur (Ctx ctx) (Cursor [] elem)"

fun is_present :: "doc_state \<Rightarrow> id \<Rightarrow> bool" where
"is_present (Ctx ctx) item = (
  case (ctx (Pres item)) of
    (Some (Ctx ops)) \<Rightarrow> (dom ops \<noteq> {}) |
    (Some _) \<Rightarrow> False |
    None \<Rightarrow> False
)" |
"is_present _ _ = False"

function get_next :: "doc_state \<Rightarrow> cursor \<Rightarrow> cursor option" where
"get_next (Ctx ctx) (Cursor [] prev_id) = (
  case (ctx (NextT prev_id)) of
    (Some (IdRef Tail)) \<Rightarrow> None |
    (Some (IdRef next_id)) \<Rightarrow> (
      if (is_present (Ctx ctx) next_id)
      then (Some (Cursor [] next_id))
      else (get_next (Ctx ctx) (Cursor [] next_id))) |
    (Some _) \<Rightarrow> None |
    None \<Rightarrow> None)" |
"get_next (Ctx ctx) (Cursor (k#ks) kn) = (
  case (ctx k) of
    (Some inner) \<Rightarrow> (
      case (get_next inner (Cursor ks kn)) of
        (Some (Cursor ks1 kn1)) \<Rightarrow> (Some (Cursor (k#ks1) kn1)) |
        None \<Rightarrow> None) |
    None \<Rightarrow> None)" |
"get_next _ _ = None"
by pat_completeness auto

fun eval_cur :: "state \<Rightarrow> expr \<Rightarrow> cursor option" where
"eval_cur _ Doc = (Some (Cursor [] Root))" |
"eval_cur (State doc vars) (Var x) = (vars x)" |
"eval_cur state (Get expr key) = (
  case (eval_cur state expr) of
    (Some (Cursor xs x)) \<Rightarrow> (Some (Cursor (xs @ [MapT x]) (Key key))) |
    None \<Rightarrow> None)" |
"eval_cur state (Iter expr) = (
  case (eval_cur state expr) of
    (Some (Cursor xs x)) \<Rightarrow> (Some (Cursor (xs @ [ListT x]) Head)) |
    None \<Rightarrow> None)" |
"eval_cur (State doc vars) (Next expr) = (
  case (eval_cur (State doc vars) expr) of
    (Some cursor) \<Rightarrow> (get_next doc cursor) |
    None \<Rightarrow> None)"

inductive valid_expr :: "state \<Rightarrow> expr \<Rightarrow> bool" for state where
expr_doc:  "valid_expr state Doc" |
expr_var:  "defined_var x state \<Longrightarrow> valid_expr state (Var x)" |
expr_get:  "valid_expr state expr \<Longrightarrow> valid_expr state (Get expr key)" |
expr_iter: "valid_expr state expr \<Longrightarrow> valid_expr state (Iter expr)" |
expr_next: "valid_expr state expr \<Longrightarrow> valid_next state expr \<Longrightarrow> valid_expr state (Next expr)"

definition empty_state :: state
where "empty_state = (State (Ctx Map.empty) Map.empty)"

lemma "valid_expr empty_state Doc"
by (rule expr_doc)

lemma "valid_expr (let_var empty_state ''hi'' (Cursor [] Root)) (Var ''hi'')"
by (simp, rule expr_var, rule expr_doc)

lemma "valid_expr empty_state (Get Doc ''hi'')"
by (rule expr_get, rule expr_doc)

lemma "valid_expr empty_state (Iter Doc)"
by (rule expr_iter, rule expr_doc)

end
