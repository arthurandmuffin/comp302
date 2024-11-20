(* Given two indices, i and k, the slice is the list containing the elements between the i'th and k'th element of the original list (both limits included).
Start counting the elements with 0 (this is the way the List module numbers elements).

# slice ["a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"; "j"] 2 6;;
- : string list = ["c"; "d"; "e"; "f"; "g"] *)

# let slice list i k =
  let rec take n = function
    | [] -> []
    | h :: t -> if n = 0 then [] else h :: take (n - 1) t
  in
  let rec drop n = function
    | [] -> []
    | h :: t as l -> if n = 0 then l else drop (n - 1) t
  in
  take (k - i + 1) (drop i list);;
val slice : 'a list -> int -> int -> 'a list = <fun>

