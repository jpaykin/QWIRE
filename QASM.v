Require Import Reals.
Require Import String.
Require Import HOASCircuits.
Require Import HOASExamples.
Require Import DBCircuits.
Require Import Arith.
Require Import List.

(* QASM.v - representation of QASM circuits *)

Definition id := string.

Inductive bexp : Type :=
| BTrue : bexp
| BFalse : bexp
| BI : string -> bexp
| BNot : bexp -> bexp
| BAnd : bexp -> bexp -> bexp
.

Inductive binop : Set :=
| plus | minus 
| times | div
| pow
.

Inductive unaryop : Set :=
| sin
| cos
| tan | e_to | ln | sqrt
| neg
.

Inductive exp : Set :=
| e_real (r:R)
| e_nat (n:nat)
| e_pi
| e_id (name:id)
| e_binop (e1:exp) (b:binop) (e2:exp)
| e_unop (u:unaryop) (e:exp)
.         

Inductive argument : Set :=
| a_id (n:id)
| a_idx (n:id) (i:nat)
.

Definition idlist := list id.
Definition anylist := list argument.
Definition explist := list exp.

Inductive uop : Set :=
| u_U (l:explist) (a:argument)
| u_CX (a1 a2:argument)
| u_app (i:id) (l:anylist)
| u_call (i:id) (es:explist) (l:anylist)
.

Inductive qop : Set :=
| q_uop (u:uop)
| q_meas (ain: argument) (aout: argument)
| q_reset (a:argument)
.          

Inductive gop : Set :=
| g_uop (u:uop)
| g_barrier (ids:idlist)
.

Definition goplist := list gop.  (* Nonempty? *)

Inductive decl : Set :=
| qreg (name:id) (size:nat)
| creg (name:id) (size:nat)
.

(*
gatedecl 
gate FOO ( ... ) <...> { ... } 
*)
Inductive statement : Set :=
| s_decl (d:decl)  
  (* TODO: what is the difference between args and names? are those the right terminology? *)
| s_gatedecl (name:id) (args:option idlist) (names:idlist) (body:goplist)
| s_opaque (name:id) (args:option idlist) (names:idlist)
| s_qop (q:qop)
| s_if (x:id) (n:nat) (q:qop)
| s_barrier (args:anylist)
| s_output (args:anylist)
| s_error (msg:string) (* msg explains about the compile error *)
.            

Definition program := list statement.

Declare Scope qasm_scope.
Notation " b1 + b2 " := (e_binop b1 plus b2) (at level 50, left associativity)
                     : qasm_scope.
Notation " b1 - b2 " := (e_binop b1 minus b2) (at level 50, left associativity)
                     : qasm_scope.
Notation " b1 * b2 " := (e_binop b1 times b2) (at level 40, left associativity)
                     : qasm_scope.
Notation " b1 / b2 " := (e_binop b1 div b2) (at level 40, left associativity)
                     : qasm_scope.
Notation " - b "     := (e_unop neg b) : qasm_scope.
Notation "0" := (e_nat 0) : qasm_scope.
Notation "2" := (e_nat 2) : qasm_scope.
Notation "4" := (e_nat 4) : qasm_scope.
Open Scope qasm_scope.
Notation pi := (e_pi).
Close Scope qasm_scope.


Open Scope R_scope.
Import ListNotations.
Require Import Notations.
Open Scope circ_scope.

(** Convert from Minimal Circuits to QASM **)

(* [Min Circuit] to [QASM] translation procedure 
   1. Transform [Unitary] gates into a sequence of universal gates (ROT3 and CNOT).
      - See [min_circuit_translation_helper], [min_circuit_merge], 
            [unitary_gate_translation], [transpose_unitary_gate_circuit], 
            [append_gate_last], and [control_unitary_gate_circuit] functions.
   2. Translate the circuit into [QASM] program
      - See [trans], [trans'], [trans_exp], [pat_to_anylist], [meta_if], 
            [meta_if_true], and [meta_if_flase] functions.
*)

Locate "()".
Definition test01 : Box One (Bit ⊗ Bit) :=
  box_ () ⇒
    gate_ a ← init0 @();
    gate_ b ← init1 @();
    gate_ a' ← meas @a;
    gate_ b' ← meas @b;
    (a', b').

Definition test01_db := hoas_to_db_box test01.

Definition test10 : Box One (Bit ⊗ Bit) :=
  box_ () ⇒
    gate_ b ← init0 @();
    gate_ a ← init1 @();
    gate_ a' ← meas @a;
    gate_ b' ← meas @b;
    (a', b').

Definition test10_db := hoas_to_db_box test10.

Eval compute in test01_db.
Eval compute in test10_db.

(** Naming functions for qreg, creg, and bits **)
Require Import Ascii.
(* Nat to string converter *)
Definition natToDigit (n : nat) : ascii :=
  match n with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
  | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
  end.
Fixpoint writeNatAux (time n : nat) (acc : string) : string :=
  let acc' := String (natToDigit (n mod 10)) acc in
  match time with
    | 0 => acc'
    | S time' =>
      match (n / 10)%nat with
        | 0 => acc'
        | n' => writeNatAux time' n' acc'
      end
  end.
Definition writeNat (n : nat) : string :=
  writeNatAux n n "".
(* naming function for qregs *)
Definition qname : nat -> id := fun x => String (ascii_of_nat 113) (writeNat x).
(* naming function for cregs *)
Definition cname : nat -> id := fun x => String (ascii_of_nat 99) (writeNat x).
(* name of the [creg array] used for branching *)
Definition bname : id := "bits"%string.
(* naming function for ith element of bits *)
Definition bname_i : nat -> id := fun i => append "bits[" (append (writeNat i) "]").

Fixpoint get_var_name (li : list string) (x : nat) : string :=
  match x with
  | 0 => match li with
        | [] => ""
        | h :: t => h
        end
  | S x' => match li with
           | [] => ""
           | h :: t => get_var_name t x'
           end
  end.
Fixpoint add_var_name (li : list string) (name : string) : list string := li ++ [name].
Fixpoint put_var_name (li : list string) (x : nat) (name : string) : list string :=
  match x with
  | 0 => match li with
        | [] => []
        | h :: t => name :: t
        end
  | S x' => match li with
           | [] => []
           | h :: t => h :: (put_var_name t x' name)
           end
  end.
Fixpoint remove_var_name (li : list string) (x : nat) : list string :=
  match x with
  | 0 => match li with
        | [] => []
        | h :: t => t
        end
  | S x' => match li with
           | [] => []
           | h :: t => h :: (remove_var_name t x')
           end
  end.

Open Scope qasm_scope.

Fixpoint process_ctrl (p : program) (ctrl_name : string) : program :=
  match p with
  | [] => []
  | h :: t =>
    match h with
    | s_if id val qop =>
      match qop with
      | q_uop (u_U [theta; phi; lambda] target_arg) =>
        let c := (a_id ctrl_name) in
        let t := target_arg in
        [s_if id val (q_uop (u_U [0; 0; (lambda-phi)/2] t));
                                             (* u1((lambda-phi)/2) t *)
           s_if id val (q_uop (u_CX c t)); (* cx c,t *)
           s_if id val (q_uop (u_U [-theta/2; 0; -(phi+lambda)/2] t));
                                             (* u3(-theta/2,0,-(phi+lambda)/2) t *)
           s_if id val (q_uop (u_CX c t)); (* cx c,t *)
           s_if id val (q_uop (u_U [theta/2; phi; 0] t))]
                                             (* u3(theta/2,phi,0) t *)
      | q_uop (u_CX ctrl2_arg target_arg) =>
        let a := (a_id ctrl_name) in
        let b := ctrl2_arg in
        let c := target_arg in
        [s_if id val (q_uop (u_U [pi/2;0;pi] c)); (* h c *)
           s_if id val (q_uop (u_CX b c));          (* cx b,c *)
           s_if id val (q_uop (u_U [0;0;-pi/4] c)); (* tdg c *)
           s_if id val (q_uop (u_CX a c));          (* cx a,c *)
           s_if id val (q_uop (u_U [0;0;pi/4] c));  (* t c *)
           s_if id val (q_uop (u_CX b c));          (* cx b,c *)
           s_if id val (q_uop (u_U [0;0;-pi/4] c)); (* tdg c *)
           s_if id val (q_uop (u_CX a c));          (* cx a,c *)
           s_if id val (q_uop (u_U [0;0;pi/4] b));  (* t b *)
           s_if id val (q_uop (u_U [0;0;pi/4] c));  (* t c *)
           s_if id val (q_uop (u_U [pi/2;0;pi] c)); (* h c *)
           s_if id val (q_uop (u_CX a b));          (* cx a,b *)
           s_if id val (q_uop (u_U [0;0;pi/4] a));  (* t a *)
           s_if id val (q_uop (u_U [0;0;-pi/4] b)); (* tdg b *)
           s_if id val (q_uop (u_CX a b))]          (* cx a,b *)
      | _ => [s_error "db_gate Unitary ctrl process error"]
      end
    | s_qop qop =>
      match qop with
      | q_uop (u_U [theta; phi; lambda] target_arg) =>
        let c := (a_id ctrl_name) in
        let t := target_arg in
        [s_qop (q_uop (u_U [0; 0; (lambda-phi)/2] t));
                                                    (* u1((lambda-phi)/2) t *)
           s_qop (q_uop (u_CX c t));                (* cx c,t *)
           s_qop (q_uop (u_U [-theta/2; 0; -(phi+lambda)/2] t));
                                                    (* u3(-theta/2,0,-(phi+lambda)/2) t *)
           s_qop (q_uop (u_CX c t));                (* cx c,t *)
           s_qop (q_uop (u_U [theta/2; phi; 0] t))] (* u3(theta/2,phi,0) t *)
      | q_uop (u_CX ctrl2_arg target_arg) =>
        let a := (a_id ctrl_name) in
        let b := ctrl2_arg in
        let c := target_arg in
        [s_qop (q_uop (u_U [pi/2;0;pi] c));   (* h c *)
           s_qop (q_uop (u_CX b c));          (* cx b,c *)
           s_qop (q_uop (u_U [0;0;-pi/4] c)); (* tdg c *)
           s_qop (q_uop (u_CX a c));          (* cx a,c *)
           s_qop (q_uop (u_U [0;0;pi/4] c));  (* t c *)
           s_qop (q_uop (u_CX b c));          (* cx b,c *)
           s_qop (q_uop (u_U [0;0;-pi/4] c)); (* tdg c *)
           s_qop (q_uop (u_CX a c));          (* cx a,c *)
           s_qop (q_uop (u_U [0;0;pi/4] b));  (* t b *)
           s_qop (q_uop (u_U [0;0;pi/4] c));  (* t c *)
           s_qop (q_uop (u_U [pi/2;0;pi] c)); (* h c *)
           s_qop (q_uop (u_CX a b));          (* cx a,b *)
           s_qop (q_uop (u_U [0;0;pi/4] a));  (* t a *)
           s_qop (q_uop (u_U [0;0;-pi/4] b)); (* tdg b *)
           s_qop (q_uop (u_CX a b))]          (* cx a,b *)
      | _ => [s_error "db_gate Unitary ctrl process error"]
      end
    | _ => [s_error "db_gate Unitary ctrl process error"]
    end ++ (process_ctrl t bname)
  end.

Fixpoint process_transpose (p : program) : program :=
  match p with
  | [] => []
  | h :: t =>
    (process_transpose t)
      ++ match h with
         | s_if id val qop =>
           match qop with
           | q_uop (u_U [theta; phi; lambda] target_name) =>
             [s_if id val (q_uop (u_U [-theta; -phi; -lambda] target_name))]
           | q_uop (u_CX ctrl2_name target_name) =>
             [s_if id val (q_uop (u_CX ctrl2_name target_name))]
           | _ => [s_error "db_gate Unitary transpose process error"]
           end
         | s_qop (q_uop (u_U [theta; phi; lambda] target_name)) =>
           [s_qop (q_uop (u_U [-theta; -phi; -lambda] target_name))]
         | s_qop (q_uop (u_CX ctrl2_name target_name)) =>
           [s_qop (q_uop (u_CX ctrl2_name target_name))]
         | _ => [s_error "db_gate Unitary transpose process error"]
         end
  end.

Open Scope type_scope.
Close Scope circ_scope.
Program Fixpoint unitary_to_qasm {W} (li : list string) (v : nat) (u : Unitary W) (p : Pat W) : (program * nat) :=
  match u with
  | _H =>
    match p with
    | qubit x => ([s_qop (q_uop (u_U [pi/2;0;pi] (a_id (get_var_name li x))))], v)
    | unit | bit _ | pair _ _ => ([s_error "db_gate Unitary H error"], v)
    end
  | _X =>
    match p with
    | qubit x => ([s_qop (q_uop (u_U [pi;0;pi] (a_id (get_var_name li x))))], v)
    | unit | bit _ | pair _ _ => ([s_error "db_gate Unitary X error"], v)
    end
  | _Y =>
    match p with
    | qubit x => ([s_qop (q_uop (u_U [pi;pi/2;pi/2] (a_id (get_var_name li x))))], v)
    | unit | bit _ | pair _ _ => ([s_error "db_gate Unitary Y error"], v)
    end
  | _Z =>
    match p with
    | qubit x => ([s_qop (q_uop (u_U [0;0;pi] (a_id (get_var_name li x))))], v)
    | unit | bit _ | pair _ _ => ([s_error "db_gate Unitary Z error"], v)
    end
  | _R_ phi =>
    match p with
    | qubit x => ([s_qop (q_uop (u_U [0;0;e_real phi] (a_id (get_var_name li x))))], v)
    | unit | bit _ | pair _ _ => ([s_error "db_gate Unitary R error"], v)
    end
  | ctrl u' =>
    match p with
    | pair p1 p2 =>
      match p1 with
      | qubit x =>
        let (qasm_unitary, v') := (unitary_to_qasm li v u' p2) in
        ((process_ctrl qasm_unitary (get_var_name li x)), v')
      | unit | bit _ | pair _ _ => ([s_error "db_gate Unitary ctrl error"], v)
      end
    | unit | bit _ | qubit _ => ([s_error "db_gate Unitary ctrl error"], v)
    end
  | bit_ctrl u' =>
    match p with
    | pair p1 p2 =>
      match p1 with
      | bit x =>
        let (qasm_unitary, v') := (unitary_to_qasm li (S v) u' p2) in
        (([s_decl (qreg (qname v) 1);
             s_if (get_var_name li x) 1
                  (q_uop (u_U [e_pi; e_nat 0; e_pi] (a_id (qname v))))]
            ++ (process_ctrl qasm_unitary (qname v))), v')
      | unit | qubit _ | pair _ _ => ([s_error "db_gate Unitary bit_ctrl error"], v)
      end
    | unit | bit _ | qubit _ => ([s_error "db_gate Unitary bit_ctrl error"], v)
    end
  end.

Fixpoint pat_to_anylist {w} (li : list string) (p : Pat w) : anylist :=
  match p with
  | unit => []
  | qubit x => [a_id (get_var_name li x)]
  | bit x => [a_id (get_var_name li x)]
  | pair p1 p2 => (pat_to_anylist li p1) ++ (pat_to_anylist li p2)
  end.

Program Fixpoint db_to_qasm {w} (li : list string) (v : nat) (c : DeBruijn_Circuit w) : (program * nat) :=
  match c with
  | db_output p => ([s_output (pat_to_anylist li p)], v)
  | db_gate g p c' =>
    match g with
    | U u =>
      let (qasm_unitary, v') := (unitary_to_qasm li v u p) in
      let (qasm_ramnent, v'') := (db_to_qasm li v' c') in
      (qasm_unitary ++ qasm_ramnent, v'')
    | BNOT =>
      match p with
      | bit x =>
        let (qasm, v') := (db_to_qasm li (S v) c') in
        ([s_decl (qreg (qname v) 1);
            s_if (get_var_name li x) 0
                 (q_uop (u_U [e_pi; e_nat 0; e_pi] (a_id (qname v))));
            s_qop (q_meas (a_id (qname v)) (a_id (get_var_name li x)))]
           ++ qasm, v')
      | unit | qubit _ | pair _ _ => ([s_error "db_gate NOT error"], v)
      end
    | init0 =>
      match p with
      | unit =>
        let li' := add_var_name li (qname v) in
        let (qasm, v') := (db_to_qasm li' (S v) c') in
        (([s_decl (qreg (qname v) 1)] ++ qasm), v')
      | bit _ | qubit _ | pair _ _ => ([s_error "db_gate init0 error"], v)
      end
    | init1 =>
      match p with
      | unit =>
        let li' := add_var_name li (qname v) in
        let (qasm, v') := (db_to_qasm li' (S v) c') in
        (([s_decl (qreg (qname v) 1);
             s_qop (q_uop (u_U [e_pi; e_nat 0; e_pi] (a_id (qname v))))]
            ++ qasm), v')
      | bit _ | qubit _ | pair _ _ => ([s_error "db_gate init1 error"], v)
      end
    | new0 =>
      match p with
      | unit =>
        let li' := add_var_name li (cname v) in
        let (qasm, v') := (db_to_qasm li' (S v) c') in
        (([s_decl (creg (cname v) 1)] ++ qasm), v')
      | bit _ | qubit _ | pair _ _ => ([s_error "db_gate new0 error"], v)
      end
    | new1 =>
      match p with
      | unit =>
        let li' := add_var_name li (cname v) in
        let (qasm, v') := (db_to_qasm li' (S (S v)) c') in
        (([s_decl (creg (cname v) 1);
             s_decl (qreg (qname (S v)) 1);
             s_qop (q_uop (u_U [e_pi; e_nat 0; e_pi] (a_id (qname (S v)))));
             s_qop (q_meas (a_id (qname (S v))) (a_id (cname v)))]
            ++ qasm), v')
      | bit _ | qubit _ | pair _ _ => ([s_error "db_gate new1 error"], v)
      end
    | meas =>
      match p with
      | qubit x =>
        let li' := (put_var_name li x (cname v)) in
        let (qasm, v') := (db_to_qasm li' (S v) c') in
        (([s_decl (creg (cname v) 1);
             s_qop (q_meas (a_id (get_var_name li x)) (a_id (cname v)))]
            ++ qasm), v')
      | unit | bit _ | pair _ _ => ([s_error "db_gate meas error"], v)
      end
    | measQ =>
      match p with
      | qubit x =>
        let (qasm, v') := (db_to_qasm li (S v) c') in
        (([s_decl (creg (cname v) 1);
             s_qop (q_meas (a_id (get_var_name li x)) (a_id (cname v)))]
            ++ qasm), v')
      | unit | bit _ | pair _ _ => ([s_error "db_gate measQ error"], v)
      end
    | discard =>
      match p with
      | bit x =>
        let li' := (remove_var_name li x) in
        (db_to_qasm li' v c')
      | unit | qubit _ | pair _ _ => ([s_error "db_gate discard error"], v)
      end
    | assert0 | assert1 =>
      match p with
      | qubit x =>
        let li' := (remove_var_name li x) in
        (db_to_qasm li' v c')
      | unit | bit _ | pair _ _ => ([s_error "db_gate assert error"], v)
      end
    end
  | db_lift p f =>
    match p with
    | bit x =>
      let (qasm_true, v') := db_to_qasm li (S v) (f true) in
      let (qasm_false, v'') := db_to_qasm li v' (f false) in
      (([s_decl (qreg (qname v) 1);
           s_if (get_var_name li x) 1
                (q_uop (u_U [e_pi; e_nat 0; e_pi] (a_id (qname v))))]
          ++ (process_ctrl qasm_true (qname v))
          ++ [s_qop (q_uop (u_U [e_pi; e_nat 0; e_pi] (a_id (qname v))))]
          ++ (process_ctrl qasm_false (qname v))), v'')
    | qubit _ | unit | pair _ _ => ([s_error "db_lift error"], v)
    end
  end.

Definition db_to_qasm_box {w1 w2} (b : DeBruijn_Box w1 w2) : program :=
  match w1 with
  | One =>
    match b with
    | db_box _ c => fst (db_to_qasm [] 0 c)
    end
  | _ => []
  end.

Close Scope type_scope.
Close Scope qasm_scope.
