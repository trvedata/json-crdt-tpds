theory TrveSync
imports Main
begin

datatype primitive =
  Null
| EmptyMap
| EmptyList
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
  MapV "state_key \<Rightarrow> ((nat * nat) set * doc_state) option"
| ListV "(state_key * (nat * nat) set * doc_state) list"
| RegV "(nat * nat) \<Rightarrow> primitive option"

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

fun cur_path :: "cursor \<Rightarrow> state_key list" where
  "cur_path (Cursor ks kn) = ks"

fun cur_last :: "cursor \<Rightarrow> id" where
  "cur_last (Cursor ks kn) = kn"

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

fun first_present :: "(state_key * (nat * nat) set * doc_state) list \<Rightarrow> id option" where
  "first_present ((key, pres, _) # rest) = (
    if pres = {}
    then first_present rest
    else Some (get_id key)
  )"
| "first_present [] = None"

function (sequential) get_next :: "doc_state \<Rightarrow> cursor \<Rightarrow> cursor option" where
  "get_next (ListV ((key, pres, child) # rest)) (Cursor [] prev_id) = (
    if (get_id key) \<noteq> prev_id
    then get_next (ListV rest) (Cursor [] prev_id)
    else (
      case first_present rest of
        Some next_id \<Rightarrow> Some (Cursor [] next_id)
      | None \<Rightarrow> None
    )
  )"
| "get_next (ListV ((key, pres, child) # rest)) (Cursor (k#ks) kn) = (
    if key \<noteq> k
    then get_next (ListV rest) (Cursor (k#ks) kn)
    else (
      case get_next child (Cursor ks kn) of
        Some (Cursor ks1 kn1) \<Rightarrow> Some (Cursor (k#ks1) kn1)
      | None \<Rightarrow> None
    )
  )"
| "get_next (MapV map_val) (Cursor (k#ks) kn) = (
    case map_val k of
      Some (pres, child) \<Rightarrow> (
        case get_next child (Cursor ks kn) of
          Some (Cursor ks1 kn1) \<Rightarrow> Some (Cursor (k#ks1) kn1)
        | None \<Rightarrow> None
      )
    | None \<Rightarrow> None
  )"
| "get_next _ _ = None"
by pat_completeness auto
termination by (relation "measures [
  \<lambda>(doc, cur). (case cur of Cursor ks kn \<Rightarrow> size ks),
  \<lambda>(doc, cur). size doc
]") auto

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
    doc      = MapV Map.empty,
    vars     = Map.empty,
    op_ids   = {},
    queue    = {},
    send_buf = {},
    recv_buf = {}
  \<rparr>"

lemma "valid_expr empty_state Doc"
by (rule expr_doc)

lemma "valid_expr (let_var empty_state ''hi'' (Cursor [] Root)) (Var ''hi'')"
by (rule expr_var, simp)

lemma "valid_expr empty_state (Get Doc ''hi'')"
by (rule expr_get, rule expr_doc)

lemma "valid_expr empty_state (Iter Doc)"
by (rule expr_iter, rule expr_doc)

value "let_var empty_state ''hi'' (Cursor [] Root)"


fun find_elem :: "state_key \<Rightarrow> operation \<Rightarrow> (doc_state \<Rightarrow> doc_state option) \<Rightarrow> doc_state \<Rightarrow> doc_state option" where
  "find_elem search_key opn update_fn (ListV ((key, pres, child) # rest)) = (
    if key = search_key then (
      case update_fn child of
        Some child1 \<Rightarrow> (
          let pres1 = insert (op_id opn) pres
          in  Some (ListV ((key, pres1, child1) # rest)))
      | None \<Rightarrow> None
    ) else (
      case find_elem search_key opn update_fn (ListV rest) of
        Some (ListV rest1) \<Rightarrow> Some (ListV ((key, pres, child) # rest1))
      | _ \<Rightarrow> None
    )
  )"
| "find_elem search_key opn update_fn (ListV []) = None"
| "find_elem search_key opn update_fn (MapV map_val) = (
    case map_val search_key of
      Some (pres, child) \<Rightarrow> (
        case update_fn child of
          Some child1 \<Rightarrow> (
            let pres1 = insert (op_id opn) pres
            in  Some (MapV (map_val (search_key \<mapsto> (pres1, child1)))))
        | None \<Rightarrow> None
      )
    | None \<Rightarrow> (
      let child1_opt = (
        case search_key of
          MapT  _ \<Rightarrow> update_fn (MapV Map.empty)
        | ListT _ \<Rightarrow> update_fn (ListV [])
        | RegT  _ \<Rightarrow> update_fn (RegV Map.empty)
      ) in (
        case child1_opt of
          Some child1 \<Rightarrow> Some (MapV (map_val 
            (search_key \<mapsto> ({op_id opn}, child1))))
        | None \<Rightarrow> None
      )
    )
  )"
| "find_elem _ _ _ _ = None"

fun id_lessthan :: "id \<Rightarrow> id \<Rightarrow> bool" where
  "id_lessthan (Id ctr1 n1) (Id ctr2 n2) =
    ((ctr1 < ctr2) \<or> (ctr1 = ctr2 \<and> n1 < n2))"
| "id_lessthan _ _ = False"

fun apply_assign :: "operation \<Rightarrow> primitive \<Rightarrow> doc_state \<Rightarrow> doc_state option" where
  "apply_assign opn EmptyMap ctx = Some ctx"
| "apply_assign opn EmptyList ctx = Some ctx"
| "apply_assign opn val (RegV reg_val) =
    Some (RegV (reg_val ((op_id opn) \<mapsto> val)))"
| "apply_assign _ _ _ = None"

fun find_insert_pos :: "operation \<Rightarrow> (state_key * (nat * nat) set * doc_state) list \<Rightarrow> (state_key * (nat * nat) set * doc_state) list" where
  "find_insert_pos opn elems = (
    let new_id = (Id (fst (op_id opn)) (snd (op_id opn)));
      new_entry = (
        case op_mut opn of
          InsertOp EmptyMap \<Rightarrow> (MapT new_id, {op_id opn}, MapV Map.empty)
        | InsertOp EmptyList \<Rightarrow> (ListT new_id, {op_id opn}, ListV [])
        | InsertOp val \<Rightarrow> (RegT new_id, {op_id opn}, RegV (Map.empty ((op_id opn) \<mapsto> val)))
      )
    in (case elems of
      (key, pres, child) # rest \<Rightarrow> (
        if id_lessthan (get_id key) new_id
        then new_entry # (key, pres, child) # rest
        else (key, pres, child) # (find_insert_pos opn rest)
      )
    | [] \<Rightarrow> [new_entry]
    )
  )"

fun apply_insert :: "operation \<Rightarrow> id \<Rightarrow> doc_state \<Rightarrow> doc_state option" where
  "apply_insert opn Head (ListV elems) =
    Some (ListV (find_insert_pos opn elems))"
| "apply_insert opn prev_id (ListV ((key, pres, child) # rest)) = (
    let rest1_opt = (
      if prev_id = (get_id key) then (
        Some (ListV (find_insert_pos opn rest))
      ) else (
        apply_insert opn prev_id (ListV rest)
      )
    ) in (
      case rest1_opt of
        Some (ListV rest1) \<Rightarrow> Some (ListV ((key, pres, child) # rest1))
      | _ \<Rightarrow> None
    )
  )"
| "apply_insert _ _ _ = None"

fun apply_delete :: "operation \<Rightarrow> id \<Rightarrow> doc_state \<Rightarrow> doc_state option" where
  "apply_delete opn kn ctx = Some ctx" (* TODO *)

fun clear :: "operation \<Rightarrow> doc_state \<Rightarrow> doc_state option" where
  "clear opn ctx = Some ctx" (* TODO *)

fun clear_elem :: "id \<Rightarrow> operation \<Rightarrow> doc_state \<Rightarrow> doc_state option" where
  "clear_elem key opn ctx =
    Option.bind (Option.bind
      (find_elem (RegT key) opn (clear opn) ctx)
      (find_elem (MapT key) opn (clear opn)))
      (find_elem (ListT key) opn (clear opn))"

function apply_op :: "cursor \<Rightarrow> operation \<Rightarrow> doc_state \<Rightarrow> doc_state option" where
  "apply_op (Cursor (k#ks) kn) opn ctx =
    find_elem k opn (apply_op (Cursor ks kn) opn) ctx"
| "apply_op (Cursor [] kn) opn ctx = (
    case op_mut opn of
      AssignOp EmptyMap  \<Rightarrow> find_elem (MapT  kn) opn (clear opn) ctx
    | AssignOp EmptyList \<Rightarrow> find_elem (ListT kn) opn (clear opn) ctx
    | AssignOp val       \<Rightarrow> find_elem (RegT  kn) opn (apply_assign opn val) ctx
    | InsertOp val       \<Rightarrow> apply_insert opn kn ctx
    | DeleteOp           \<Rightarrow> apply_delete opn kn ctx
  )"
by pat_completeness auto
termination by (relation "measures [
  \<lambda>(cur, opn, doc). (case cur of Cursor ks kn \<Rightarrow> size ks)
]") auto

definition make_op :: "state \<Rightarrow> cursor \<Rightarrow> mutation \<Rightarrow> state list" where
  "make_op state cursor mutation = (
    let ctr = Max ((\<lambda>(c,p). c) ` (op_ids state));
        opn = \<lparr>op_id     = (ctr + 1, (peer_id state)),
               op_deps   = (op_ids state),
               op_cursor = cursor,
               op_mut    = mutation\<rparr>
    in (
      case apply_op (op_cursor opn) opn (doc state) of
        Some new_doc \<Rightarrow> [state \<lparr>
          doc    := new_doc,
          op_ids := insert (op_id opn) (op_ids state),
          queue  := insert opn (queue state)
        \<rparr>]
      | None \<Rightarrow> []
    )
  )"

fun eval_cmd :: "state \<Rightarrow> cmd \<Rightarrow> state list" where
  "eval_cmd state (LetCmd var expr) = (
    case eval_cur state expr of
      Some cursor \<Rightarrow> [let_var state var cursor]
    | None \<Rightarrow> []
  )"
| "eval_cmd state (AssignCmd expr val) = (
    case eval_cur state expr of
      Some cursor \<Rightarrow> make_op state cursor (AssignOp val)
    | None \<Rightarrow> []
  )"
| "eval_cmd state (InsertCmd expr val) = (
    case eval_cur state expr of
      Some cursor \<Rightarrow> make_op state cursor (InsertOp val)
    | None \<Rightarrow> []
  )"
| "eval_cmd state (DeleteCmd expr) = (
    case eval_cur state expr of
      Some cursor \<Rightarrow> make_op state cursor DeleteOp
    | None \<Rightarrow> []
  )"
| "eval_cmd state YieldCmd = [state]" (* TODO yield *)

end
