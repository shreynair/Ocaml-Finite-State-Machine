open List
open Sets

(*********)
(* Types *)
(*********)

type ('q, 's) transition = 'q * 's option * 'q

type ('q, 's) nfa_t = {
  sigma: 's list;
  qs: 'q list;
  q0: 'q;
  fs: 'q list;
  delta: ('q, 's) transition list;
}

(***********)
(* Utility *)
(***********)

(* explode converts a string to a character list *)
let explode (s: string) : char list =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l)
  in
  exp (String.length s - 1) []


(****************)
(* Part 1: NFAs *)
(****************)

let move (nfa: ('q,'s) nfa_t) (qs: 'q list) (s: 's option) : 'q list =
  let rec move_helper trans qs s =
    match trans with
    | [] -> []
    | (a,b,c)::tail when (elem a qs) -> 
        if b = s then
          insert c (move_helper tail qs s) 
        else
          (move_helper tail qs s) 
        
    | _::tail -> (move_helper tail qs s) 
  in

  move_helper nfa.delta qs s 

let e_closure (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list =
  let rec e_helper (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list =
    match qs with
      | qs when (eq qs (union qs (move nfa qs None)))  -> qs
      | _ -> e_helper nfa (union qs (move nfa qs None)) 
  in
  
  e_helper nfa qs


(*******************************)
(* Part 2: Subset Construction *)
(*******************************)

let new_states (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list = 
  map (fun x -> e_closure nfa (move nfa qs (Some x))) nfa.sigma

let new_trans (nfa: ('q,'s) nfa_t) (qs: 'q list) : ('q list, 's) transition list = 
  map (fun x -> (qs, Some x, e_closure nfa (move nfa qs (Some x)))) nfa.sigma

let new_finals (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list = 
  match (intersection qs nfa.fs) with [] -> [] | head::tail -> [qs]

let rec nfa_to_dfa_step (nfa: ('q,'s) nfa_t) (dfa: ('q list, 's) nfa_t)
    (work: 'q list list) : ('q list, 's) nfa_t =
    match work with 
      | [] -> dfa
      | head::tail -> 
        let dfa_new_states = new_states nfa head in
        let dfa_new_trans = new_trans nfa head in
        let dfa_new_finals = new_finals nfa head in
        nfa_to_dfa_step nfa {sigma = dfa.sigma; qs = insert_all [head] dfa.qs  ; q0 = dfa.q0; fs = insert_all dfa_new_finals dfa.fs; delta = insert_all dfa_new_trans dfa.delta} 
        (diff (insert_all dfa_new_states tail) (insert_all [head] dfa.qs))

let nfa_to_dfa (nfa: ('q,'s) nfa_t) : ('q list, 's) nfa_t = 
  nfa_to_dfa_step nfa {sigma = nfa.sigma; qs = [e_closure nfa [nfa.q0]]; q0 = e_closure nfa [nfa.q0]; fs = []; delta = []} [(e_closure nfa [nfa.q0])] 

(* Accept Function *)
let accept (nfa: ('q,char) nfa_t) (s: string) : bool = 
  let s_list = explode s in
  let dfa = nfa_to_dfa nfa in

  let rec accept_helper (nfa: ('q list,char) nfa_t) (str_lst: char list) (curr: 'q list ) : bool =
    match str_lst with
      | [] when (elem curr nfa.fs)  -> true
      | head::tail when (elem head nfa.sigma) = true -> 
        let trans =
          match (move nfa [curr] (Some head)) with
            | [] -> []
            | head::tail -> head
        in

        accept_helper nfa tail trans
      | _ -> false
  in
  
  accept_helper dfa s_list dfa.q0
