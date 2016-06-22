theory TrveSync
imports Main
begin

datatype primitive =
  Null
| Str string
| Int int
| Bool bool

datatype expr =
  Doc
| Var string
| Get expr string
| Iter expr
| Next expr

datatype cmd =
  LetCmd string expr
| AssignCmd expr primitive
| InsertCmd expr primitive
| DeleteCmd expr
| YieldCmd

datatype id =
  Root
| Head
| Id nat nat
| Key string

datatype state_key =
  MapT  id
| ListT id
| RegT  id

datatype doc_state =
  Prim primitive
| IdRef id
| Ctx "(state_key * id set * doc_state) list"

datatype cursor = Cursor "state_key list" id

datatype mutation =
  AssignOp primitive
| InsertOp primitive
| DeleteOp

record operation =
  op_id     :: "nat * nat"
  op_deps   :: "(nat * nat) set"
  op_cursor :: cursor
  op_mut    :: mutation

record state =
  peer_id  :: nat
  doc      :: doc_state
  vars     :: "string \<Rightarrow> cursor option"
  op_ids   :: "(nat * nat) set"
  queue    :: "operation set"
  send_buf :: "operation set"
  recv_buf :: "operation set"

fun defined_var :: "string \<Rightarrow> state \<Rightarrow> bool" where
  "defined_var x state =
    (x \<in> dom (vars state))"

fun let_var :: "state \<Rightarrow> string \<Rightarrow> cursor \<Rightarrow> state" where
  "let_var state key val =
    state \<lparr>vars := (vars state)(key \<mapsto> val)\<rparr>"

fun get_id :: "state_key \<Rightarrow> id" where
  "get_id (MapT  x) = x"
| "get_id (ListT x) = x"
| "get_id (RegT  x) = x"

fun first_present :: "(state_key * id set * doc_state) list \<Rightarrow> id option" where
  "first_present ((key, pres, _) # rest) = (
    if pres = {}
    then first_present rest
    else Some (get_id key)
  )"
| "first_present [] = None"

fun get_next :: "doc_state \<Rightarrow> cursor \<Rightarrow> cursor option" where
  "get_next (Ctx ((key, pres, child) # rest)) (Cursor [] prev_id) = (
    if (get_id key) \<noteq> prev_id
    then get_next (Ctx rest) (Cursor [] prev_id)
    else (
      case first_present rest of
        Some next_id \<Rightarrow> Some (Cursor [] next_id)
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
  "eval_cur state Doc = Some (Cursor [] Root)"
| "eval_cur state (Var x) = (vars state) x"
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
| "eval_cur state (Next expr) = (
    case eval_cur state expr of
      Some cursor \<Rightarrow> get_next (doc state) cursor
    | None \<Rightarrow> None
  )"

fun valid_next :: "state \<Rightarrow> expr \<Rightarrow> bool" where
  "valid_next state expr = (
    case eval_cur state expr of
      Some cursor \<Rightarrow> (get_next (doc state) cursor) \<noteq> None
    | None \<Rightarrow> False
  )"

inductive valid_expr :: "state \<Rightarrow> expr \<Rightarrow> bool" for state where
expr_doc:  "valid_expr state Doc" |
expr_var:  "defined_var x state \<Longrightarrow> valid_expr state (Var x)" |
expr_get:  "valid_expr state expr \<Longrightarrow> valid_expr state (Get expr key)" |
expr_iter: "valid_expr state expr \<Longrightarrow> valid_expr state (Iter expr)" |
expr_next: "valid_expr state expr \<Longrightarrow> valid_next state expr \<Longrightarrow> valid_expr state (Next expr)"

definition empty_state :: state where
  "empty_state = \<lparr>
    peer_id  = 1,
    doc      = Ctx [],
    vars     = Map.empty,
    op_ids   = {},
    queue    = {},
    send_buf = {},
    recv_buf = {}
  \<rparr>"

lemma "valid_expr empty_state Doc"
by (rule expr_doc)

lemma "valid_expr (let_var empty_state ''hi'' (Cursor [] Root)) (Var ''hi'')"
by (simp, rule expr_var, rule expr_doc)

lemma "valid_expr empty_state (Get Doc ''hi'')"
by (rule expr_get, rule expr_doc)

lemma "valid_expr empty_state (Iter Doc)"
by (rule expr_iter, rule expr_doc)

value "let_var empty_state ''hi'' (Cursor [] Root)"

definition make_op :: "state \<Rightarrow> cursor \<Rightarrow> mutation \<Rightarrow> state" where
  "make_op state cursor mutation = (
    let ctr = Max ((\<lambda>(c,p). c) ` (op_ids state));
        opn = \<lparr>op_id     = (ctr + 1, (peer_id state)),
               op_deps   = (op_ids state),
               op_cursor = cursor,
               op_mut    = mutation\<rparr>
    in  state \<lparr>op_ids := insert (op_id opn) (op_ids state),
               queue  := insert opn (queue state)\<rparr>
  )"

fun eval_cmd :: "state \<Rightarrow> cmd \<Rightarrow> state list" where
  "eval_cmd state (LetCmd var expr) = (
    case eval_cur state expr of
      Some cursor \<Rightarrow> [let_var state var cursor]
    | None \<Rightarrow> []
  )"
| "eval_cmd state (AssignCmd expr val) = (
    case eval_cur state expr of
      Some cursor \<Rightarrow> [make_op state cursor (AssignOp val)]
    | None \<Rightarrow> []
  )"
| "eval_cmd state (InsertCmd expr val) = (
    case eval_cur state expr of
      Some cursor \<Rightarrow> [make_op state cursor (InsertOp val)]
    | None \<Rightarrow> []
  )"
| "eval_cmd state (DeleteCmd expr) = (
    case eval_cur state expr of
      Some cursor \<Rightarrow> [make_op state cursor DeleteOp]
    | None \<Rightarrow> []
  )"
| "eval_cmd state YieldCmd = [state]" (* TODO yield *)

end
