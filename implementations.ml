(* 1. Naive approach: Iterate through, take / drop based on index*)
(* Not tail recursive - Call stack grows n *)
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

(* Similar to 1 i think?*)
(* Need to check what's under the hood *)
let slice list i k =
  list
  |> List.drop i
  |> List.take (k - i + 1)

(* Need to check what's under the hood *)
let slice list i k =
  List.filteri (fun idx _ -> idx >= i && idx <= k) list


(* List.fold_left *)
let slice list i k =
  List.rev (fst (List.fold_left (fun (acc, idx) x ->
    if idx >= i && idx <= k then 
      (x :: acc, idx + 1)
    else 
      (acc, idx + 1)
  ) ([], 0) list))

(* 4. Tail-recursive: CPS *)
(* Similar to acc, more flexibility, can perform operation to each sliced index value *)
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