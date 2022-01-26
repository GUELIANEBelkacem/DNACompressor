exception Bad_format of string
(*declaration type arbre*)
type arbre=
|Vide
|Noeud of arbre * int * arbre
|Fleche of arbre ref * int array
|CNoeudTemp of arbre * int * arbre * int ref
|CFleche of arbre * int array
|CNoeud of arbre * int * arbre * int



(*supprimer le n'eme element d'une liste*)
let rec cut (l : int list) (n : int) : int list =
    if n = 0 then
    match l with
    |[] -> []
    |a::b -> b

    else
    match l with
    |[] -> []
    |a::b -> a::cut b (n-1)

(*generation d'une liste 1:n*)
let rec gen_list (l : int list) (n : int) (t : int): int list =
    let l = [] in
    begin match t with
    | 0 -> l
    | _ -> (n-t+1)::gen_list l n (t-1)
    end;;


(*---------------------------------------------------------------------------------------*)

let extraction_alea (l: int list) (r: int list) : (int list * int list) =
    let taille = List.length l  in
        Random.self_init ();
        let nombre = Random.int taille in
            let p = List.nth l nombre in
                (cut l nombre,p::r)

(*---------------------------------------------------------------------------------------*)


(*repeter extraction_alea n fois*)
let rec repeter_extraction_alea (k : int list * int list) (n : int ) : (int list * int list) =
    let l = fst k in
        let r = snd k in
            if n=0 then (l,r)
            else let (l,r) = extraction_alea l r in repeter_extraction_alea (l,r) (n-1);;



(*---------------------------------------------------------------------------------------*)

let gen_permutation (n : int ) : int list =
    let vide = [] in
        let r = [] in
            let l = gen_list vide n n in
                let result = snd (repeter_extraction_alea (l,r) (n)) in
                result ;;

(*---------------------------------------------------------------------------------------*)

(*print des listes*)
let rec print_listy l t  =
    let n = List.length l in
        match t with
        | 0 -> print_string " "
        | _ ->print_int (List.nth l (n-t)); print_string " "; print_listy l (t-1)



(*print des arbres*)
let rec print_abr abr =
match abr with
| Vide -> print_string ""
| Noeud(lft, n, rgt) -> print_abr lft; print_abr rgt
| Fleche(a, b) -> begin  match !a with  | CNoeud(x, y, z, t) -> print_int y; print_string "\n" |_-> raise(Bad_format "blabla")end
| CFleche(a, b) -> begin  match a with  | CNoeud(x, y, z, t) -> print_int y; print_string "\n" end
| CNoeud(lft, n, rgt, taille) -> print_abr lft; print_abr rgt(*print_abr lft; print_int n; print_string "\n"; print_abr rgt*)


(*constructeur d'arbres*)
let cstr_abr lst =
  let rec construction_abr l arb =
    let rec inserer n a =
      match a with
      |Vide -> Noeud(Vide, n, Vide)
      |Noeud(lft, e, rgt) -> if n < e then Noeud(inserer n lft, e, rgt)
        else Noeud(lft, e, inserer n rgt)
    in match l with
    |[] -> arb
    |h::t -> construction_abr t (inserer h arb)
  in construction_abr lst Vide


(*fonction phi pour generer les strings de comparaison*)
let rec phi abr =
begin match abr with
| Vide -> ""
| Noeud(lft, n, rgt) -> String.concat "" ["("; (phi lft); ")"; (phi rgt)]
| Fleche(a, b) -> ""
end;;


(*generateur des listes prefixe a partir des arbres*)
let prefixe abr =
  let rec prefixe_list a =
    match a with
    | Vide -> []
    | Noeud(lft, n, rgt) -> List.concat [[n]; (prefixe_list lft); (prefixe_list rgt)]
    | Fleche(a, b) -> []
    | CNoeud(lft, n, rgt, taille) ->[]
  in Array.of_list (prefixe_list abr)

(*fonction de compression*)
(*........................................................................................................*)



let rec tailles abr=
match abr with
  | Vide -> 0
  | Noeud(l, n, r) -> raise (Bad_format "Noeud lors de la taille")
  | CNoeudTemp(l, n, r, taille) -> let x =(1 + (tailles l) + (tailles r)) in taille := x; x
  | Fleche(a, b) -> (Array.length b)
  |_-> raise (Bad_format "il reste des Fleche dans l'arbre compressé")

let rec taille_final abr =
  match abr with
  |Vide-> Vide
  |CNoeudTemp(l, n, r, taille) -> CNoeud(taille_final l, n, taille_final r, !taille)
  |Fleche(a, b) -> abr
  |_-> raise (Bad_format "il reste des Fleche/Noeud dans l'arbre compressé")



let rec ntocn abr =
match abr with
  | Vide -> Vide
  | Noeud(l, n, r) -> CNoeudTemp(ntocn l, n, ntocn r, ref 0)
  | CNoeud(l, n, r, taille) -> CNoeud(l, n, r, taille)
  | Fleche(a, b) -> Fleche(a, b)


let rec recherche_noeud abr n =
  match abr with
  |Vide -> raise(Bad_format "le noeud recherché nexiste pas")
  |CNoeud(l, m, r, t) -> if n < m then recherche_noeud l n
	else if m = n then abr
  else recherche_noeud r n
  |Noeud(_,_,_)-> raise (Bad_format "erreur lors de la recherche noeud")
  |Fleche(_)-> raise (Bad_format "erreur lors de la recherche fleche")
  |CFleche(_)-> raise (Bad_format "erreur lors de la recherche cfleche")


let is_fleche_correspondant n a =
  match a with
  |Fleche(a, l) -> if Array.get l 0 = n then true else false
  |_-> false

let is_parent n abr=
  match abr with
  |Vide -> raise(Bad_format "le noeud recherché nexiste pas")
  |CNoeud(l, m, r, t) -> if is_fleche_correspondant n l = true then 1 else
    if is_fleche_correspondant n r then 2 else 0
  |_-> raise (Bad_format "erreur lors de is_parent")

let rec remplacer_sous_arbre sabr abr =
  match sabr with
  |CFleche(a, l) -> begin
      match abr with
      |CNoeud(lf, m, rt, ta) -> if is_parent (Array.get l 0) abr = 1 then CNoeud(sabr, m, rt, ta) else
        if is_parent (Array.get l 0) abr = 2 then CNoeud(lf, m, sabr, ta) else
        if (Array.get l 0) < m then CNoeud(remplacer_sous_arbre sabr lf, m, rt, ta) else
          CNoeud(lf, m, remplacer_sous_arbre sabr rt, ta)
      |_-> raise (Bad_format "erreur lors de remplacer ss arbre")
    end
  |_-> raise (Bad_format "erreur lors de remplacer ss arbre")




let rec contient_fleche a =
  match a with
  |Vide -> false
  |Fleche(_, _) -> true
  |CNoeud(l, n, r, t) -> if contient_fleche l = false then contient_fleche r else
      true
  |CFleche(_, _) -> false
  |_-> raise (Bad_format "l'arbre compressé ne doit pas contenir de Noeud")


let rec reorienter_fleches a=
  let rec reorienter_fleche abr origin =
    match abr with
    |Vide -> Vide
    |CFleche(_,_) -> Vide
    |CNoeud(l, n, r, t) -> let a = reorienter_fleche l origin in
      if a = Vide then reorienter_fleche r origin else a
    |Fleche(a, lt) -> begin
      match !a with
        |Noeud(l, v, r) -> remplacer_sous_arbre (CFleche(recherche_noeud origin v, lt)) origin
        |_-> raise (Bad_format "fleche invalide")
    end
    |Noeud(_) -> raise(Bad_format "On ne doit pas avoir de Noeud dans un Carbre")
  in if contient_fleche a = false then a
  else reorienter_fleches (reorienter_fleche a a)



let rec recherche_struct chaine abr =
  match abr with
  |Vide -> Vide
  |Noeud(l, e, r) -> if String.equal (phi abr) chaine then abr
    else let temp = recherche_struct chaine l in
      if temp = Vide then recherche_struct chaine r
      else temp
  |Fleche(a, b) -> Vide

let rec compress_abr abr =
  let rec constr_compr sous_abr a =
 	match sous_abr with
	|Vide -> Vide
	|Noeud(l, e, r) -> let t = recherche_struct (phi sous_abr) a in
  	if t = Vide then Vide
  	else if (t == sous_abr) then Noeud(constr_compr l a, e, constr_compr r a)
  	else Fleche(ref(t), prefixe sous_abr)
	|Fleche(a,b) -> sous_abr
  in let res = constr_compr abr abr
  in let v1 = ntocn res
  in let v2 = tailles v1
  in let v3 = taille_final v1
  in let v4 = reorienter_fleches v3



  in v4

(*........................................................................................................*)


(*fonction de recherche (retourne true ou false)*)
(*........................................................................................................*)
let rec recherche_vect abr vect v i =

  if i >= (Array.length vect) then false
  else if (Array.get vect i)= v then true
  else

  match abr with
  | CNoeud(l, n, r, taille) ->  if (Array.get vect i)> v then recherche_vect l vect v (i+1)
  else begin match l with
    | CNoeud(x, y, z, t) -> recherche_vect r vect v (i+t)
            | Vide -> recherche_vect r vect v (i+1)
            | Noeud(l, n, r) -> false
            | CFleche(a, b) -> recherche_vect r vect v (i+(Array.length b))
        end
  | Vide -> false
  | Noeud(l, n, r) -> false
  | CFleche(a, b) -> recherche_vect a vect v (i)



let rec recherche abr v =
match abr with
| Vide -> false
| Noeud(l, n, r) -> if n=v then true
                    else if v<n then recherche l v
                    else recherche r v
| CFleche(a, b) -> let i = 0 in recherche_vect (a) b v i

| CNoeud(l, n, r, taille) -> if n=v then true
                    else if v<n then recherche l v
                    else recherche r v


(*........................................................................................................*)

(*tests*)
let printb b=
if (b==true) then print_string "it's here\n" else print_string "nope\n"

(*........................................................................................................*)
let time f =
  let t = Sys.time() in
  let res = f () in
 (Sys.time() -. t)
;;

let rec searchit abr i =
match i with
| 0-> ()
| _ -> let y = recherche abr i in searchit abr (i-1)
(*........................................................................................................*)
let x = cstr_abr ([4;2;3;8;1;9;6;7;5]);;
print_abr x;;
let y = compress_abr x;;
print_abr y;;

(*........................................................................................................*)
let intercale list1 list2 =
  let rec intercaler l1 l2 n1 n2 =
    Random.self_init ();
    let n = n1 + n2 in
    if n = 0 then []
    else
    let r = (Random.int n) in
      if r<n1 then
      match l1 with
      | [] -> l2
      | h::t -> h::(intercaler t l2 (n1-1) n2)
      else
      match l2 with
      | [] -> l1
      | h::t -> h::(intercaler l1 t n1 (n2-1))
  in intercaler list1 list2 (List.length list1) (List.length list2)

let rec gen_permutation2 p q =
  if p > q then []
  else if p = q then  p::[]
  else intercale (gen_permutation2 p ((p+q)/2)) (gen_permutation2 (((p+q)/2) + 1) q)




let rec size_test i s=
match i with
| 1000-> s
| _ -> let l = gen_permutation i in let x = cstr_abr (l) in let y = compress_abr x
in let sizeof (x: arbre) : int = Obj.reachable_words (Obj.repr x)
in let stri = String.concat "" [s; string_of_int i; "  "; string_of_int (sizeof x); "  "; string_of_int (sizeof y);"       "; string_of_float (time (fun () -> (searchit x i))); "  "; string_of_float (time (fun () -> (searchit y i))); "\n"]
in
if (i<10) then size_test (i+1) stri
else if (i<100) then size_test (i+10) stri
else if (i<1000) then size_test (i+100) stri
else if (i<10000) then size_test (i+1000) stri
else size_test (i+10000) stri



let rec time_test i s=
match i with
| 6000-> s
| _ -> let l = gen_permutation i in let x = cstr_abr (l) in let y = compress_abr x
in let stri = String.concat "" [s; string_of_int i; "  "; string_of_float (time (fun () -> (searchit x i))); "  "; string_of_float (time (fun () -> (searchit y i))); "\n"]
in if (i<10) then time_test (i+1) stri
else if (i<100) then time_test (i+10) stri
else if (i<1000) then time_test (i+100) stri
else if (i<10000) then time_test (i+1000) stri
else time_test (i+10000) stri




open Printf

let file = "test.txt"
let message = size_test 1 ""

let () =

  let oc = open_out file in
  fprintf oc "%s\n" message;
  close_out oc;;

(*........................................................................................................*)




