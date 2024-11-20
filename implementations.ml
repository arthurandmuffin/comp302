(* 1. Naive approach from ocaml website: Iterate through, take / drop based on index*)

(* Use Case: Simple slicing for small lists where performance is not critical.
   Efficiency: O(n), not tail-recursive; the call stack grows linearly with the list size.
   Correctness: Correct for valid indices, but may fail or return unexpected results for invalid indices. *)

let slice list i k =
  let rec take n = function
    | [] -> []
    | h :: t -> 
      if n = 0 then
        []
      else
        h :: take (n - 1) t

  let rec drop n = function
    | [] -> []
    | h :: t as l ->
      if n = 0 then
        l
      else
        drop (n - 1) l

  take (k - i + 1) (drop i list)

  (* Call: slice lst ('a list) i (start index) k (end index) *)


(* 2. Tail-recursive: Accumulator *)

(* Use Case: Suitable for large lists where stack overflow is a concern.
   Efficiency: O(n), tail-recursive; constant stack space.
   Correctness: Handles indices correctly, but requires careful handling of the accumulator and indices. *)

let rec slice_accum list i k acc =
  if k < 0 then List.rev acc
  else match list with
  | [] -> List.rev acc
  | x :: t ->
    if i > 0 then
      slice t (i - 1) (k - 1) acc
    else
      slice t 0 (k - 1) (x :: acc)

(* Call: slice lst ('a list) i (start index) k (end index) [] ('a list)*)

(* Proof for tail recursion

THEOREM: For all l, i, k, acc. slice_accum l i k acc = List.rev acc @ slice_naive l i k

Induction on l

Base Case: l = []

slice_accum [] i k acc
  ==> List.rev acc               by program slice_accum

List.rev acc @ slice_naive [] i k
  ==> List.rev acc @ []          by program slice_naive
  ==> List.rev acc               by list concatenation

Therefore, slice_accum [] i k acc evaluates to the same value as List.rev acc @ slice_naive [] i k


Step Case: l = x::xs

IH : slice_accum xs i k acc = List.rev acc @ slice_naive xs i k

TO PROVE: slice_accum (x::xs) i k acc = List.rev acc @ slice_naive (x::xs) i k

Case 1: i > 0

slice_accum (x::xs) i k acc
  ==> slice_accum xs (i - 1) (k - 1) acc           by program slice_accum

List.rev acc @ slice_naive (x::xs) i k
  ==> List.rev acc @ slice_naive xs (i - 1) k      by program slice_naive

By IH:
slice_accum xs (i - 1) (k - 1) acc = List.rev acc @ slice_naive xs (i - 1) k

Therefore, slice_accum (x::xs) i k acc = List.rev acc @ slice_naive (x::xs) i k

Case 2: i = 0, k >= 0

slice_accum (x::xs) 0 k acc
  ==> slice_accum xs 0 (k - 1) (x :: acc)           by program slice_accum

List.rev acc @ slice_naive (x::xs) 0 k
  ==> List.rev acc @ (x :: slice_naive xs 0 (k - 1)) by program slice_naive

By IH (choosing acc' = (x :: acc)):
slice_accum xs 0 (k - 1) acc' = List.rev acc' @ slice_naive xs 0 (k - 1)

Therefore:
List.rev acc @ (x :: slice_naive xs 0 (k - 1)) = List.rev acc' @ slice_naive xs 0 (k - 1)

MAIN THEOREM: For all l, i, k, acc. slice_accum l i k acc = List.rev acc @ slice_naive l i k

Base Case and Step Case have both been proven. Therefore, by induction, the theorem holds.
 *)



(* 3. Higher Order Functions*)

(* Option A: Using tail-recursive List.drop and List.take *)

(* Use Case: Readability and concise code.
    Efficiency: Each function is O(n), combined O(n). .
    Correctness:  *)

let slice list i k =
  list
  |> drop i
  |> take (k - i + 1)
  
  (* Under the hood, drop is tail recursive but take is using @tail_mod_cons. 
  Therefore, this implementation has a space complexity of O(n), which is fine
  for small to medium sized lists, but starts to affect performance at larger sizes. *)

  (* Tail-recursive drop *)
  let drop n l =
    let rec aux i = function
      | _x::l when i < n -> aux (i + 1) l
      | rest -> rest
    in
    if n < 0 then invalid_arg "List.drop";
    aux 0 l

  (* Take *)
  let take n l =
    let[@tail_mod_cons] rec aux n l =
      match n, l with
      | 0, _ | _, [] -> []
      | n, x::l -> x::aux (n - 1) l
    in
    if n < 0 then invalid_arg "List.take";
    aux n l


(* Proof for List.drop and List.take

THEOREM: For all l, i, k. slice_drop_take l i k = slice_naive l i k

Induction on l

Base Case: l = []

slice_drop_take [] i k
  ==> take (k - i + 1) (drop i [])                 by program slice_drop_take
  ==> take (k - i + 1) []                          by definition of drop
  ==> []                                           by definition of take

slice_naive [] i k
  ==> []                                           by program slice_naive

Therefore, slice_drop_take [] i k and slice_naive [] i k both evaluate to []


Step Case: l = x::xs

IH : slice_drop_take xs i k = slice_naive xs i k

TO PROVE: slice_drop_take (x::xs) i k = slice_naive (x::xs) i k

Case 1: i > 0

slice_drop_take (x::xs) i k
  ==> take (k - i + 1) (drop i (x::xs))             by program slice_drop_take
  ==> take (k - i + 1) (drop (i - 1) xs)            by definition of drop

slice_naive (x::xs) i k
  ==> slice_naive xs (i - 1) k                      by program slice_naive

By IH:
slice_drop_take xs (i - 1) k = slice_naive xs (i - 1) k

Therefore:
slice_drop_take (x::xs) i k = slice_naive (x::xs) i k

Case 2: i = 0, k >= 0

slice_drop_take (x::xs) 0 k
  ==> take (k - 0 + 1) (drop 0 (x::xs))             by program slice_drop_take
  ==> take (k + 1) (x::xs)                          by definition of drop

slice_naive (x::xs) 0 k
  ==> x :: slice_naive xs 0 (k - 1)                 by program slice_naive

By definition of take:
take (k + 1) (x::xs) = x :: take k xs

By IH:
take k xs = slice_naive xs 0 (k - 1)

Therefore:
x :: take k xs = x :: slice_naive xs 0 (k - 1)

MAIN THEOREM: For all l, i, k. slice_drop_take l i k = slice_naive l i k

Base Case and Step Case have both been proven. Therefore, by induction, the theorem holds. *)


(* Option B: Using List.filteri *)

(* Use Case: When you need to apply a condition based on index.
   Efficiency: O(n), iterates through the entire list.
   Correctness: Correct if indices are within bounds. *)

let slice list i k =
  List.filteri (fun idx _ -> idx >= i && idx <= k) list


(* Proof for List.filteri

THEOREM: For all l, i, k. slice_filteri l i k = slice_naive l i k

Induction on l

Base Case: l = []

slice_filteri [] i k
  ==> []                                 by program slice_filteri

slice_naive [] i k
  ==> []                                 by program slice_naive

Therefore, slice_filteri [] i k and slice_naive [] i k both evaluate to []


Step Case: l = x::xs

IH : slice_filteri xs i k = slice_naive xs i k

TO PROVE: slice_filteri (x::xs) i k = slice_naive (x::xs) i k

Case 1: i > 0

slice_filteri (x::xs) i k
  ==> slice_filteri xs (i - 1) (k - 1)             by program slice_filteri

slice_naive (x::xs) i k
  ==> slice_naive xs (i - 1) k                     by program slice_naive

By IH:
slice_filteri xs (i - 1) (k - 1) = slice_naive xs (i - 1) k

Therefore, slice_filteri (x::xs) i k = slice_naive (x::xs) i k

Case 2: i = 0, k >= 0

slice_filteri (x::xs) 0 k
  ==> x :: slice_filteri xs 0 (k - 1)              by program slice_filteri

slice_naive (x::xs) 0 k
  ==> x :: slice_naive xs 0 (k - 1)                by program slice_naive

By IH:
slice_filteri xs 0 (k - 1) = slice_naive xs 0 (k - 1)

Therefore:
x :: slice_filteri xs 0 (k - 1) = x :: slice_naive xs 0 (k - 1)

MAIN THEOREM: For all l, i, k. slice_filteri l i k = slice_naive l i k

Base Case and Step Case have both been proven. Therefore, by induction, the theorem holds. *)



(* Option C: Using List.fold_left *)

(* Use Case: Functional style slicing; can be adapted for additional processing.
   Efficiency: O(n), traverses the entire list.
   Correctness: Correct slicing but less efficient due to full traversal. *)

let slice list i k =
  List.rev (fst (List.fold_left (fun (acc, idx) x ->
    if idx >= i && idx <= k then 
      (x :: acc, idx + 1)
    else 
      (acc, idx + 1)
  ) ([], 0) list))


(* Proof for List.fold_left

THEOREM: For all l, i, k. slice_fold l i k = slice_naive l i k

Induction on l

Base Case: l = []

slice_fold [] i k
  ==> List.rev (fst (List.fold_left (fun (acc, idx) x -> if idx >= i && idx <= k then (x :: acc, idx + 1) else (acc, idx + 1)) ([], 0) []))
  ==> [] by program slice_fold

slice_naive [] i k
  ==> [] by program slice_naive

Therefore, slice_fold [] i k and slice_naive [] i k both evaluate to []


Step Case: l = x::xs

IH : slice_fold xs i k = slice_naive xs i k

TO PROVE: slice_fold (x::xs) i k = slice_naive (x::xs) i k

Case 1: i > 0

slice_fold (x::xs) i k
  ==> List.rev (fst (List.fold_left (fun (acc, idx) x -> if idx >= i && idx <= k then (x :: acc, idx + 1) else (acc, idx + 1)) ([], 1) xs))

By IH:
slice_fold xs (i - 1) k = slice_naive xs (i - 1) k

Therefore:
slice_fold (x::xs) i k = slice_naive (x::xs) i k

Case 2: i = 0, k >= 0

slice_fold (x::xs) 0 k
  ==> List.rev (fst (List.fold_left (fun (acc, idx) x -> if idx >= 0 && idx <= k then (x :: acc, idx + 1) else (acc, idx + 1)) ([], 0) (x::xs)))

slice_naive (x::xs) 0 k
  ==> x :: slice_naive xs 0 (k - 1)                by program slice_naive

By IH:
slice_fold xs 0 (k - 1) = slice_naive xs 0 (k - 1)

Therefore:
List.rev (fst (List.fold_left (fun (acc, idx) x -> if idx >= 0 && idx <= k then (x :: acc, idx + 1) else (acc, idx + 1)) ([], 0) (x::xs))) = slice_naive (x::xs) 0 k

MAIN THEOREM: For all l, i, k. slice_fold l i k = slice_naive l i k

Base Case and Step Case have both been proven. Therefore, by induction, the theorem holds. *)


(* 4. Tail-recursive: CPS *)

(* Use Case: Additional operations. Useful when chaining computations.
    Efficiency: O(n), tail-recursive; efficient for large lists.
    Correctness: Correct and flexible, but more complex to understand and use. Less readable.*)

let slice list i k cont =
  let rec drop_cps n lst cont =
    match lst with
    | [] -> cont []
    | _ :: t -> 
      if n = 0 then 
        cont lst 
      else 
        drop_cps (n - 1) t cont
  in
  let rec take_cps n lst cont =
    match lst with
    | [] -> cont []
    | h :: t -> 
      if n = 0 then 
        cont [] 
      else 
        take_cps (n - 1) t (fun rest -> cont (h :: rest))
  in
  drop_cps i list (fun dropped_list ->
    take_cps (k - i + 1) dropped_list cont)

(* Call w/ CPS *)
let res = ref []
let () = slice [1; 2; 3; 4; 5] 1 3 (fun res -> result := res)


(* Proof for CPS

THEOREM: For all l, i, k, cont. cont (slice_naive l i k) = slice_cps l i k cont

Induction on l

Base Case: l = []

slice_naive [] i k
  ==> []                           by program slice_naive

slice_cps [] i k cont
  ==> cont []                      by program slice_cps

Therefore, cont (slice_naive [] i k) and slice_cps [] i k cont both evaluate to cont []  


Step Case: l = x::xs  

IH : for i, k, cont. cont (slice_naive xs i k) = slice_cps xs i k cont

TO PROVE: cont (slice_naive (x::xs) i k) = slice_cps (x::xs) i k cont

Case 1: i > 0 

slice_naive (x::xs) i k
  ==> slice_naive xs (i - 1) k        by program slice_naive

cont (slice_naive (x::xs) i k)
  ==> cont (slice_naive xs (i - 1) k)  by substitution

slice_cps (x::xs) i k cont
  ==> slice_cps xs (i - 1) k cont      by program slice_cps

By IH, cont (slice_naive xs (i - 1) k) = slice_cps xs (i - 1) k cont

Therefore, cont (slice_naive (x::xs) i k) = slice_cps (x::xs) i k cont


Case 2: i = 0, k >= 0

slice_naive (x::xs) 0 k
  ==> x :: slice_naive xs 0 (k - 1)    by program slice_naive

cont (slice_naive (x::xs) 0 k)
  ==> cont (x :: slice_naive xs 0 (k - 1))  by substitution

slice_cps (x::xs) 0 k cont
  ==> slice_cps xs 0 (k - 1) (fun rest -> cont (x :: rest))   by program slice_cps

By IH (choosing cont' = (fun rest -> cont (x :: rest))):

cont' (slice_naive xs 0 (k - 1)) = slice_cps xs 0 (k - 1) cont'

Therefore, cont (x :: slice_naive xs 0 (k - 1)) = slice_cps (x::xs) 0 k cont


MAIN THEOREM: For all l, i, k, cont. cont (slice_naive l i k) = slice_cps l i k cont.

Base Case and Step Case have both been proven. Therefore, by induction:

For all l, i, k, cont, cont (slice_naive l i k) evaluates to the same value as slice_cps l i k cont.
*)


(* O(k) in other programming languages since accessing any single element in a list/array is O(1). (k length of sliced list)
But in Ocaml, lists are recursively defined, meaning that it behaves more like a linked list, meaning the O(1) is impossible.
Solution: Array in Ocaml *)

let array = Array.of_list list
(* O(n), very good if repeated slicing needed, as any slicing operation after is O(k) instead of O(n)*)
let slice_array arr i k =
  Array.sub arr i (k - i + 1)


(* Proof for array implementation

THEOREM: For all l, i, k. slice_array l i k = slice_naive l i k

Induction on l

Base Case: l = []

slice_array [] i k
  ==> Array.sub (Array.of_list []) i (k - i + 1)   by program slice_array
  ==> Array.sub [||] i (k - i + 1)                 by definition of Array.of_list
  ==> [||]                                        by definition of Array.sub

slice_naive [] i k
  ==> []                                           by program slice_naive

By converting the empty array back to a list:
Array.to_list [||] = []

Therefore, slice_array [] i k and slice_naive [] i k both evaluate to []


Step Case: l = x::xs

IH : slice_array xs i k = slice_naive xs i k

TO PROVE: slice_array (x::xs) i k = slice_naive (x::xs) i k

Case 1: i > 0

slice_array (x::xs) i k
  ==> Array.sub (Array.of_list (x::xs)) i (k - i + 1)   by program slice_array
  ==> Array.sub (Array.of_list xs) (i - 1) (k - i + 1)  by definition of Array.of_list and drop semantics

slice_naive (x::xs) i k
  ==> slice_naive xs (i - 1) k                          by program slice_naive

By IH:
slice_array xs (i - 1) k = slice_naive xs (i - 1) k

Therefore:
slice_array (x::xs) i k = slice_naive (x::xs) i k

Case 2: i = 0, k >= 0

slice_array (x::xs) 0 k
  ==> Array.sub (Array.of_list (x::xs)) 0 (k - 0 + 1)   by program slice_array
  ==> Array.sub (Array.of_list (x::xs)) 0 (k + 1)

slice_naive (x::xs) 0 k
  ==> x :: slice_naive xs 0 (k - 1)                     by program slice_naive

Converting the result of Array.sub back to a list:
Array.to_list (Array.sub (Array.of_list (x::xs)) 0 (k + 1)) = x :: Array.to_list (Array.sub (Array.of_list xs) 0 k)

By IH:
Array.to_list (Array.sub (Array.of_list xs) 0 k) = slice_naive xs 0 (k - 1)

Therefore:
x :: Array.to_list (Array.sub (Array.of_list xs) 0 k) = x :: slice_naive xs 0 (k - 1)

MAIN THEOREM: For all l, i, k. slice_array l i k = slice_naive l i k

Base Case and Step Case have both been proven. Therefore, by induction, the theorem holds. *)


