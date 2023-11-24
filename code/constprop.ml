open Ll
open Datastructures

(* The lattice of symbolic constants ---------------------------------------- *)
module SymConst =
  struct
    type t = NonConst           (* Uid may take on multiple values at runtime *)
           | Const of int64     (* Uid will always evaluate to const i64 or i1 *)
           | UndefConst         (* Uid is not defined at the point *)

    let compare s t =
      match (s, t) with
      | (Const i, Const j) -> Int64.compare i j
      | (NonConst, NonConst) | (UndefConst, UndefConst) -> 0
      | (NonConst, _) | (_, UndefConst) -> 1
      | (UndefConst, _) | (_, NonConst) -> -1

    let to_string : t -> string = function
      | NonConst -> "NonConst"
      | Const i -> Printf.sprintf "Const (%LdL)" i
      | UndefConst -> "UndefConst"

    
  end

(* The analysis computes, at each program point, which UIDs in scope will evaluate 
   to integer constants *)
type fact = SymConst.t UidM.t



(* flow function across Ll instructions ------------------------------------- *)
(* - Uid of a binop or icmp with const arguments is constant-out
   - Uid of a binop or icmp with an UndefConst argument is UndefConst-out
   - Uid of a binop or icmp with an NonConst argument is NonConst-out
   - Uid of stores and void calls are UndefConst-out
   - Uid of all other instructions are NonConst-out
 *)
let insn_flow (u,i:uid * insn) (d:fact) : fact =
  let to_symconst op = 
    begin match op with 
    | Id i -> UidM.find_or SymConst.UndefConst d i 
    | Const i -> SymConst.Const i 
    | _ -> SymConst.NonConst
    end in 

  let merge s1 s2 =
    match s1, s2 with
    | SymConst.NonConst, _ | _, SymConst.NonConst -> SymConst.NonConst
    | SymConst.Const i, SymConst.Const j when Int64.compare i j == 0 -> SymConst.Const i
    | SymConst.Const _, SymConst.Const _ -> SymConst.NonConst
    | SymConst.UndefConst, i | i, SymConst.UndefConst -> i in 

  let binop b op1 op2 = 
    begin match b, op1, op2 with 
    | _, SymConst.NonConst, _ | _, _, SymConst.NonConst -> SymConst.NonConst 
    | _, SymConst.UndefConst, _ | _, _, SymConst.UndefConst -> SymConst.UndefConst 
    | Add, SymConst.Const i1, SymConst.Const i2 -> SymConst.Const (Int64.add i1 i2) 
    | Sub, SymConst.Const i1, SymConst.Const i2 -> SymConst.Const (Int64.sub i1 i2)
    | Mul, SymConst.Const i1, SymConst.Const i2 -> SymConst.Const (Int64.mul i1 i2)  
    | Shl, SymConst.Const i1, SymConst.Const i2 -> SymConst.Const (Int64.shift_left i1 (Int64.to_int i2))
    | Lshr, SymConst.Const i1, SymConst.Const i2 -> SymConst.Const (Int64.shift_right_logical i1 (Int64.to_int i2)) 
    | Ashr, SymConst.Const i1, SymConst.Const i2 -> SymConst.Const (Int64.shift_right i1 (Int64.to_int i2))  
    | And, SymConst.Const i1, SymConst.Const i2 -> SymConst.Const (Int64.logand i1 i2)  
    | Or, SymConst.Const i1, SymConst.Const i2 -> SymConst.Const (Int64.logor i1 i2)  
    | Xor, SymConst.Const i1, SymConst.Const i2 -> SymConst.Const (Int64.logxor i1 i2)   
    end in 

  let icmp cond op1 op2 = 
    let to_int64_bool = function | true -> 1L | false -> 0L in 
    begin match cond, op1, op2 with  
    | _, SymConst.NonConst, _ | _, _, SymConst.NonConst -> SymConst.NonConst 
    | _, SymConst.UndefConst, _ | _, _, SymConst.UndefConst -> SymConst.UndefConst 
    | Eq, SymConst.Const i1, SymConst.Const i2 -> SymConst.Const (to_int64_bool (Int64.compare i1 i2 == 0))
    | Ne, SymConst.Const i1, SymConst.Const i2 -> SymConst.Const (to_int64_bool (Int64.compare i1 i2 != 0))
    | Slt, SymConst.Const i1, SymConst.Const i2 -> SymConst.Const (to_int64_bool (Int64.compare i1 i2 < 0))
    | Sle, SymConst.Const i1, SymConst.Const i2 -> SymConst.Const (to_int64_bool (Int64.compare i1 i2 <= 0)) 
    | Sgt, SymConst.Const i1, SymConst.Const i2 -> SymConst.Const (to_int64_bool (Int64.compare i1 i2 > 0))
    | Sge, SymConst.Const i1, SymConst.Const i2 -> SymConst.Const (to_int64_bool (Int64.compare i1 i2 >= 0))
    end in 

  let process_insn ins = 
    (match i with 
      | Binop (b, _, op1, op2) -> binop b (to_symconst op1) (to_symconst op2) 
      | Icmp (b, _, op1, op2) -> icmp b (to_symconst op1) (to_symconst op2) 
      | Store _ | Call (Void, _, _) -> SymConst.UndefConst 
      | _ -> SymConst.NonConst 
    ) in 
  
  UidM.update_or SymConst.UndefConst (merge @@ process_insn i) u d

(* The flow function across terminators is trivial: they never change const info *)
let terminator_flow (t:terminator) (d:fact) : fact = d

(* module for instantiating the generic framework --------------------------- *)
module Fact =
  struct
    type t = fact
    let forwards = true

    let insn_flow = insn_flow
    let terminator_flow = terminator_flow
    
    let normalize : fact -> fact = 
      UidM.filter (fun _ v -> v != SymConst.UndefConst)

    let compare (d:fact) (e:fact) : int  = 
      UidM.compare SymConst.compare (normalize d) (normalize e)

    let to_string : fact -> string =
      UidM.to_string (fun _ v -> SymConst.to_string v)

    (* The constprop analysis should take the meet over predecessors to compute the
       flow into a node. You may find the UidM.merge function useful *)
    let combine (ds:fact list) : fact = 
      let merge s1 s2 =
        match s1, s2 with
        | SymConst.NonConst, _ | _, SymConst.NonConst -> SymConst.NonConst
        | SymConst.Const i, SymConst.Const j when Int64.compare i j == 0 -> SymConst.Const i
        | SymConst.Const _, SymConst.Const _ -> SymConst.NonConst
        | SymConst.UndefConst, i | i, SymConst.UndefConst -> i in 
      
      let merge_function k xo yo = 
        begin match xo, yo with 
        | None, yo | yo, None -> yo 
        | Some x, Some y -> Some (merge x y) 
        end in 

      let combine_aux d1 d2 =
        UidM.merge merge_function d1 d2
      in
      List.fold_left combine_aux UidM.empty ds
  end

(* instantiate the general framework ---------------------------------------- *)
module Graph = Cfg.AsGraph (Fact)
module Solver = Solver.Make (Fact) (Graph)

(* expose a top-level analysis operation ------------------------------------ *)
let analyze (g:Cfg.t) : Graph.t =
  (* the analysis starts with every node set to bottom (the map of every uid 
     in the function to UndefConst *)
  let init l = UidM.empty in

  (* the flow into the entry node should indicate that any parameter to the
     function is not a constant *)
  let cp_in = List.fold_right 
    (fun (u,_) -> UidM.add u SymConst.NonConst)
    g.Cfg.args UidM.empty 
  in
  let fg = Graph.of_cfg init cp_in g in
  Solver.solve fg

(* run constant propagation on a cfg given analysis results ----------------- *)
(* HINT: your cp_block implementation will probably rely on several helper 
   functions.                                                                 *)

let run (cg:Graph.t) (cfg:Cfg.t) : Cfg.t =
  let open SymConst in
  
  let cp_operand d op =
    match op with
    | Id i -> 
      (match UidM.find_or UndefConst d i with
        | Const n -> Ll.Const n
        | _ -> op)
    | _ -> op
    
  in

  let cp_instr cb (u,i) = 
    let f = cp_operand (cb u) in
    u, match i with
       | Alloca _          -> i
       | Load (t, op)        -> Load (t, f op)
       | Binop (bop, t,op1, op2) -> Binop (bop, t,f op1, f op2)
       | Icmp (cnd, t, op1, op2)  -> Icmp (cnd, t, f op1, f op2)
       | Store (t, op1, op2)     -> Store (t, f op1, f op2)
       | Bitcast (t1, op, t2)   -> Bitcast (t1, f op, t2)
       | Call (t, op, args)   -> Call (t, f op, List.map (fun (t,op) -> t, f op) args)
       | Gep (t, op, ops)      -> Gep (t, f op, List.map f ops)
  in

  let cp_terminator cb (id, t) : uid * terminator =
    let f = cp_operand (cb id) in
    id, match t with
    | Cbr (o, k, l)   -> Cbr (f o, k, l)
    | Ret (t, Some o) -> Ret (t, Some (f o))
    | Ret (_, None) | Br _ ->  t
  in

  

  let cp_block (l:Ll.lbl) (cfg:Cfg.t) : Cfg.t =
    let b = Cfg.block cfg l in
    let cb = Graph.uid_out cg l in
    let insns = List.map (cp_instr cb) b.insns in
    let term = cp_terminator cb b.term in
    Cfg.add_block l {insns; term} cfg

  in

  LblS.fold cp_block (Cfg.nodes cfg) cfg
