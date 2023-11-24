(** Dead Code Elimination  *)
open Ll
open Datastructures


(* expose a top-level analysis operation ------------------------------------ *)
(* TASK: This function should optimize a block by removing dead instructions
   - lb: a function from uids to the live-OUT set at the 
     corresponding program point
   - ab: the alias map flowing IN to each program point in the block
   - b: the current ll block

   Note: 
     Call instructions are never considered to be dead (they might produce
     side effects)

     Store instructions are not dead if the pointer written to is live _or_
     the pointer written to may be aliased.

     Other instructions are dead if the value they compute is not live.

   Hint: Consider using List.filter
 *)
let dce_block (lb:uid -> Liveness.Fact.t) 
              (ab:uid -> Alias.fact)
              (b:Ll.block) : Ll.block =
  let {insns; term} = b in 
  let aux_func (cur_uid, cur_insn) = 
    begin match cur_insn with
    | Call _ -> true
    | Store(_, _, Id op_uid) -> 
      let retrieve_set = lb cur_uid in 
      let retrieve_map = ab cur_uid in 
      (UidM.find_or (Alias.SymPtr.MayAlias) (retrieve_map) (op_uid)) = Alias.SymPtr.MayAlias ||
      UidS.find_opt (op_uid) (retrieve_set) != None
    | _ -> 
      let retrieve_set = lb cur_uid in 
      UidS.find_opt (cur_uid) (retrieve_set) != None
    end in
  let filtered_insns = List.filter (aux_func) (insns) in 
  {insns= filtered_insns; term}
  (* failwith "dce not implemented" *)

let run (lg:Liveness.Graph.t) (ag:Alias.Graph.t) (cfg:Cfg.t) : Cfg.t =

  LblS.fold (fun l cfg ->
    let b = Cfg.block cfg l in

    (* compute liveness at each program point for the block *)
    let lb = Liveness.Graph.uid_out lg l in

    (* compute aliases at each program point for the block *)
    let ab = Alias.Graph.uid_in ag l in 

    (* compute optimized block *)
    let b' = dce_block lb ab b in
    Cfg.add_block l b' cfg
  ) (Cfg.nodes cfg) cfg

