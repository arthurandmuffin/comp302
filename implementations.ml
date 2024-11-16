(* 1. Naive approach: Iterate through, take / drop based on index*)

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

let rec slice list i k acc =
  if k < 0 then List.rev acc
  else match list with
  | [] -> List.rev acc
  | x :: t ->
    if i > 0 then
      slice t (i - 1) (k - 1) acc
    else
      slice t 0 (k - 1) (x :: acc)

(* Call: slice lst ('a list) i (start index) k (end index) [] ('a list)*)

(* 3. Higher Order Functions*)

(* Option A: Using tail-recursive List.drop and List.take *)

(* Use Case: Readability and concise code for medium to large lists.
    Efficiency: Each function is O(n), combined O(n). Tail-recursive, therefore efficient stack usage.
    Correctness:  *)

let slice list i k =
  list
  |> drop i
  |> take (k - i + 1)
  
  (* Under the hood, both drop and take are tail-recursive. Therefore, this implementation is tail-recursive and stack-efficient. *)

  (* Tail-recursive drop *)
  let rec drop n lst =
    match n, lst with
    | n, lst when n <= 0 -> lst
    | _, [] -> []
    | n, _ :: t -> drop (n - 1) t

  (* Tail-recursive take with accumulator *)
  let take n lst =
    let rec aux n lst accum =
      match n, lst with
      | 0, _ | _, [] -> List.rev accum
      | n, h :: t -> aux (n - 1) t (h :: accum)
    in
    aux n lst []

(* Option B: Using List.filteri *)

(* Use Case: When you need to apply a condition based on index.
   Efficiency: O(n), iterates through the entire list.
   Correctness: Correct if indices are within bounds. *)

let slice list i k =
  List.filteri (fun idx _ -> idx >= i && idx <= k) list

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

(* O(k) in other programming languages since accessing any single element in a list/array is O(1). (k length of sliced list)
But in Ocaml, lists are recursively defined, meaning that it behaves more like a linked list, meaning the O(1) is impossible.
Solution: Array in Ocaml *)

let array = Array.of_list list
(* O(n), very good if repeated slicing needed, as any slicing operation after is O(k) instead of O(n)*)
let slice_array arr i k =
  Array.sub arr i (k - i + 1)





(* THEOREM: For all l, i, k, cont. cont (slice_naive l i k) = slice_cps l i k cont

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
