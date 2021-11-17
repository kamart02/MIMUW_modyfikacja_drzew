(*
  Zadanie: Modyfikacja drzew
  Data: 12.11.2021
  Autor: Arutr Kamieniecki (nr albumu 438500)
  Peer review'er: Oskar Pruszyński
  MIMUW 1. rok - studia informatyczne
*)

type interval = int * int
;;

(* drzewo avl z przedziałem jako wartość
   lewe poddrzewo * przedzial * prawe poddrzewo *
   * wysokość drzewa * suma długości wszystkich przedziałów 
   drzewo zawsze zawiera rozłączne przedziały *)
type t = 
  | Empty
  | Node of t * interval * t * int * int

(* funkcje wewnętrzne *)

(* porównanie przedziałów
   1 jeżeli (a,b) jest większe niż (c, d)
   -1 jeżeli mniejsze
   0 równe *)
let cmp (a, b) (c, d) = 
  if a > c then
    1
  else if a < c then
    -1
  else 
    if b < d then
      -1
    else if b > d then
      1
    else 
      0
;;

(* zwraca ilość elementów w przedziale *)
let interval_length (a, b) = 
  let lenght = b - a + 1
  in if lenght <=0 then (* jeżeli długość jest ujemna to znaczy, że nastąpiło przekoczenie max_int *)
    max_int
  else lenght
;;

(* dodawanie bez przekraczania max_int *)
let sum_without_overflow a b =
  let sum = a + b 
  in
    if sum < 0 then
      max_int
    else
      sum
;;

(* suma wszytkich elementów w drzewie zawierającym rozłączne przedziały *)
let get_length set = 
  match set with
  | Node (_, _, _, _, n) -> n
  | Empty -> 0
;;

let add_lenghts l i r = 
  let lenght_of_subtrees = 
    sum_without_overflow (get_length l) (get_length r)
  in
    sum_without_overflow lenght_of_subtrees (interval_length i)
;;

let height = function
  | Node (_, _, _, h, _) -> h
  | Empty -> 0
;;

(* łączenie dwóch drzew avl i przedziału, 
   drzewa muszą być wysokości o maksymalnej różnicy wysokości mniejszej
   niż 2 
   wynikiem jest drzewo AVL *)
let make l i r = 
  Node (l, i, r, max (height l) (height r) + 1, add_lenghts l i r)

(* balansowanie drzew avl o różnicy wyskokoći większej niż 1
   wynikiem jest drzewo AVL z przedziałem i w korzeniu *)
let bal l i r =
  let hl = height l in
  let hr = height r in
  if hl > hr + 2 then
    match l with
    | Node (ll, lk, lr, _, _) ->
        if height ll >= height lr then make ll lk (make lr i r)
        else
          (match lr with
          | Node (lrl, lrk, lrr, _, _) ->
              make (make ll lk lrl) lrk (make lrr i r)
          | Empty -> assert false)
    | Empty -> assert false
  else if hr > hl + 2 then
    match r with
    | Node (rl, rk, rr, _, _) ->
        if height rr >= height rl then make (make l i rl) rk rr
        else
          (match rl with
          | Node (rll, rlk, rlr, _, _) ->
              make (make l i rll) rlk (make rlr rk rr)
          | Empty -> assert false)
    | Empty -> assert false
  else Node (l, i, r, max hl hr + 1, add_lenghts l i r)
;;

(* minimalny element drzewa AVL *)
let rec min_elt = function
  | Node (Empty, i, _, _, _) -> i
  | Node (l, _, _, _, _) -> min_elt l
  | Empty -> raise Not_found
;;

(* drzewo AVL bez minimalnego elementu *)
let rec remove_min_elt = function
  | Node (Empty, _, r, _, _) -> r
  | Node (l, i, r, _, _) -> bal (remove_min_elt l) i r
  | Empty -> invalid_arg "PSet.remove_min_elt"
;;

(* dodanie przedziału x rozłącznego ze wszystkimi przedziałami w drzewie
   wynikiem jest drzewo AVL z przedziałem x *)
let rec add_one x = function
  | Node (l, i, r, h, n) ->
      let c = cmp x i in
      if c = 0 then Node (l, x, r, h, n)
      else if c < 0 then
        let nl = add_one x l in
        bal nl i r
      else
        let nr = add_one x r in
        bal l i nr
  | Empty -> Node (Empty, x, Empty, 1, interval_length x)
;;

(* łączenie drzew AVL o różnych wyskościach
   przedział i musi być większy niż przedziały w l i mniejszy niż w r 
   wynikiem jest drzewo AVL z i w korzniu *)
let rec join l i r =
  match (l, r) with
    (Empty, _) -> add_one i r
  | (_, Empty) -> add_one i l
  | (Node(ll, li, lr, lh, _), Node(rl, ri, rr, rh, _)) ->
      if lh > rh + 2 then bal ll li (join  lr i r) else
      if rh > lh + 2 then bal (join l i rl) ri rr else
      make l i r
;;

(* łączenie drzew AVL o różnych wyskościach
   przedziały w l muszą być mniejsze niż w r
   wynikiem jest drzewo AVL z najmniejszym przedziałem w r w korzeniu *)
let merge l r =
  match (l, r) with
  | (Empty, _) -> r
  | (_, Empty) -> l
  | _ ->
      let i = min_elt r in
      join l i (remove_min_elt r)
;;

(* funkcja zwraza 0 jeżeli x zawarte jest w przedziale i
   -1 gdzy x jest mniejszy niż przedział i
   1 jeżeli większy *)
let contains x ((a, b) as i)= 
  if a<=x && x<=b then
    0
  else
    cmp (x, x) i
;;

exception IntervalNotFound
;;

(* funkcja zwraca przedział z drzewa set w którym zawarte jest x
   w przypadku gdy taki nie istnieje wznoszony jest wyjątek *)
let rec find_interval_containing x set =
  match set with
  | Node (l, i, r, _, _) ->
    let c = contains x i
    in
      if c = 0 then
        i
      else if c > 0 then
        find_interval_containing x r
      else 
        find_interval_containing x l
  | Empty -> raise IntervalNotFound
;;

(* funkcje zewnętrzne *)

let empty = Empty
;;

let is_empty set = 
  set = Empty
;;

let split x set =
  let rec loop x = function
      Empty ->
        (Empty, false, Empty)
    | Node (l, ((a, b) as i), r, _, _) ->
        let c = contains x i in
        if c = 0 then 
          (* w przypadku gdy x znajduje się w przedziale i należy dodać do
             lewego i prawego poddrzewa odpowiednio przedziały powstałe z usunięcia
             elementu x z przedziału i *)
          let new_l = 
            if x <> min_int && x <> a then
              add_one (a, x - 1) l
            else if x <> min_int then
              l
            else
              Empty
          and new_r =
            if x <> max_int && x <> b then
              add_one (x + 1, b) r
            else if x <> max_int then
              r
            else
              Empty
          in
            (new_l, true, new_r)
        else if c < 0 then
          let (ll, pres, rl) = loop x l in (ll, pres, join rl i r)
        else
          let (lr, pres, rr) = loop x r in (join l i lr, pres, rr)
  in
    loop x set 
;;

let remove (a, b) set =
  let (left_part, _, _) = split a set
  and (_, _, right_part) = split b set
  in
    merge left_part right_part

let add (a, b) set =
  (* sprawdzenie czy przedział (a, b) jest sąsiedni lub zawarty w innym przedziale w drzewie set *)
  let new_a = 
    if a <> min_int then
      try fst (find_interval_containing (a - 1) set) with
        IntervalNotFound -> a
    else 
      min_int
  and new_b = 
    if b <> max_int then
      try snd (find_interval_containing (b + 1) set) with
        IntervalNotFound -> b
    else
      max_int
  in
    (* usunięcie nowego przedziału, aby powsatło drzewo z przedziałami rozłącznymi do (new_a, new_b) *)
    let new_set = remove (new_a, new_b) set
    in
      add_one (new_a, new_b) new_set
;;

let mem x set = 
  try 
    let _ = find_interval_containing x set 
    in
      true
  with
    IntervalNotFound -> false
;;

let iter f set =
  let rec loop = function
    | Empty -> ()
    | Node (l, i, r, _, _) -> loop l; f i; loop r 
  in
    loop set
;;

let fold f set acc =
  let rec loop acc = function
    | Empty -> acc
    | Node (l, i, r, _, _) ->
          loop (f i (loop acc l)) r 
  in
    loop acc set
;;

let elements set = 
  let rec loop acc = function
    | Empty -> acc
    | Node(l, i, r, _, _) -> loop (i :: loop acc r) l in
  loop [] set

let below x set = 
  if x <> max_int then
    let (intervals_below, _, _) = split (x + 1) set
    in
      get_length intervals_below
  else
    get_length set