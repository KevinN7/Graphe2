(*-------------transformation du graphe en listes (visibles)----------------------
*)

(* fonction qui liste les sommets *)
(* liste_v: Digraph.t -> Vertex list *)
let liste_v g = (fold_vertex (fun v qt -> v::qt) 
                               g
                               [])
;;

(* fonction qui liste les sommets et leur label *)
(* liste_v: Digraph.t -> int*int list *)
let liste_vl g = (fold_vertex (fun v qt -> (V.label v,Mark.get v)::qt) 
                               g
                               [])
;;


(* fonction qui liste les aretes *)
(* liste_e: Digraph.t -> int*int list *) 
let liste_e g = 
        (fold_edges  (fun v1 v2 qt -> (V.label v1,V.label v2)::qt) 
                     g
                     [])
;;

(* fonction qui liste les aretes et leur label *)
(* liste_e: Digraph.t -> int*int*int list *) 
let liste_el g = 
        (fold_edges  (fun v1 v2 qt -> (V.label v1,V.label v2,E.label (find_edge g v1 v2))::qt) 
                     g
                     [])
;;

(* fct liste les predecesseur*)

(*enlever liste_pred*)
let liste_pred v g =
  fold_pred (fun v l -> v::l ) g v [];;

let sans_dependance g =
  fold_vertex (fun v l -> if(in_degree g v = 0) then v::l else l) g [];; 

let appartient v l = 
  List.fold_right (fun s b -> b||v=s) l false;;

let inclu ens1 ens2 =
  List.fold_right (fun v b -> (appartient v ens2) && b) ens1 true;;

 (* entrees: 
   - un DAG
   sorties:
   - une liste des sommets du DAG ordonnées selon un tri topologique 
   specifs: 
   - vous implementerez l'algorithme 1 de l'enonce, en utilisant un format de file pour Y (section 1)
   *) 
  
let tri_topologique g = 
  let y = sans_dependance g in
         let rec iter y z = 
           match y with
           |t::q -> 
                 let newz = t::z in
                   let newy = fold_succ (fun v l -> if(inclu (liste_pred v g) newz) then l@[v] else l) g t q
                       in t::(iter newy newz)
           |[] -> []
         in iter y [];;

(* trace d'execution 
   definie en Section 2 de l'enonce (voir Figure 2)
*)
(*type Trace = (Vertex list) list ;;*)		 
		 			
(*let ordonnanceur_ressources_illimitees g =
  let y = sans_dependance g in
		let rec iter1 y z res1 =
			match y with
			|t::q->
				let rec iter2 ycourant yfutur z res = 
					match ycourant with
					|t::q -> 
						let newz = t::z in
							let newy  = fold_succ (fun v l -> if(inclu (liste_pred v g) newz) then l@[v] else l) g t q
						in iter2 q yfutur@newy newz res@[t]
					|[] -> res::iter1
				in (iter2 y [] z [])::res1
			|[] -> res1
		in iter1 y [] [];;*)
		

let etage y z g =
	let rec iter ycourant yfutur z res = 
		match ycourant with
		|t::q -> 
                    let newz=t::z in 
                        let newy  = fold_succ (fun v l -> if(inclu (liste_pred v g) newz) then l@[v] else l) g t yfutur
		        in iter q newy newz (res@[t])
		|[] -> (res,yfutur,z)
	in iter y [] z [];;
		
		
let ordonnanceur_ressources_illimitees g =
  let rec iter y z res =
	match y with
	|[]-> res
	|_ -> let (resetage,yfutur,newz) = etage y z g in iter yfutur newz (res@[resetage])
  in iter (sans_dependance g) [] [];;
		
		 
(*******************************************************************)	

  let etage_res y z nbres g=
	let rec iter ycourant yfutur z resultat nbres = 
		match ycourant with
		|t::q -> 
			if(nbres-1>=0) then
				let newz=t::z in
                                        let newy  = fold_succ (fun v l -> if(inclu (liste_pred v g) newz) then l@[v] else l) g t yfutur
				in iter q newy newz (resultat@[t]) (nbres-1)
			else (resultat,yfutur@ycourant,z)
		|[] -> (resultat,yfutur,z)
	in iter y [] z [] nbres;;
	
	(*let etage_res y z nbres=
	let rec iter ycourant yfutur z resultat nbres = 
		match ycourant with
		|t::q -> 
			if(nbres- Vertex.mass t  >=0) then
				let newz=t::z and newy  = fold_succ (fun v l -> if(inclu (liste_pred v g) newz) then l@[v] else l) g t yfutur
				in iter q newy newz resultat@[t] (nbres-  Vertex.mass t)
			else iter q yfutur@[t] z resultat nbres
		|[] -> (resultat,yfutur,z)
	in iter y [] z [] nbres;;*)

(* entrees: 
   - un nombre entier de ressources
   - un DAG
   sorties:
   - une trace d'execution du DAG 
   specifs: 
   - le DAG est suppose non pondere
   - les ressources sont supposees limitees (section 2.2)
   - vous n'utiliserez pas d'heuristique
   *)
let ordonnanceur_ressources_limitees_sans_heuristique nbres g =
  let rec iter y z res =
	match y with
	|[]-> res
	|_ -> let (resetage,yfutur,newz) = etage_res y z nbres g in iter yfutur newz (res@[resetage])
  in iter (sans_dependance g) [] [];;

  

let max a b = if(a>=b) then a else b;;

let prof_max v g =
	let rec iter v g courant =
	let lsucc = succ g v in
		match lsucc with
		|[]->courant
		|_->List.fold_right (fun t l -> max l (iter t g (courant+1)) ) lsucc 0
	in iter v g 0;;

(*let prof_max2 v g=		
	let rec iter v g courant = fold_succ (fun v a-> max a (iter v g (courant+1))) g v 0 in iter v g 0;;

	List.sort (fun a b -> let pa=prof_max a and pb=prof_max b in if pa>pb then 1 else if pa<pb then -1 else 0) liste
	
	Appliquer un tri pour ces vertex avant la selection *)
	
	
(* entrees: 
   - un nombre entier de ressources
   - un DAG
   sorties:
   - une trace d'execution du DAG 
   specifs: 
   - le DAG est suppose non pondere
   - les ressources sont supposees limitees (section 2.2)
   - vous utiliserez une heuristique pour ameliorer la duree de la trace 
   *)
   (*	List.sort (fun a b -> if(a > b)then 1 else(if(a = b)then 0 else -1))*)

let ordonnanceur_ressources_limitees_avec_heuristique nbres g =
  let rec iter y z res =
	match y with
	|[]-> res
	|_ -> let yordre = List.sort (fun a b -> let pa=prof_max a g and
        pb=prof_max b g in if pa>pb then 1 else if pa<pb then -1 else 0) y in 
			let (resetage,yfutur,newz) = etage_res yordre z nbres g in iter yfutur newz (res@[resetage])
  in iter (sans_dependance g) [] [];;
   
   
(*
let ordonnanceur_ressources_limitees_avec_heuristique nbres g = 
  let rec iter y z res =
	match y with
	|[]-> res
	|_ -> let (resetage,yfutur,newz) = etage_res y z nbres in 
	let yfutur_sort =List.sort (fun a b -> if(Vertex.mass a > Vertex.mass b)then -1 else(if(Vertex.mass a = Vertex.mass b)then 0 else 1)) in
		iter yfutur_sort newz res@[resetage]
  in iter (sans_dependance g) [] [];;*)

  (*creer un noeud de nom spécifié et l'ajoute au graphe*)
let aux nom g =
	let a=V.create(nom,1) in add_vertex g a;a;;
	
(*ajoute une chaine de noeud relier entre eux de n noeuds et renvoit le premier et le dernier*)
let prim g n nom =
	let prem = aux (nom^(string_of_int n)) g in
	let rec iter n v =
	match n with
	|0-> (prem,v)
	|_-> let tmp = aux (nom^(string_of_int n)) g in 
                add_edge g v tmp;
                iter (n-1) tmp
	in iter (n-1) prem;;

(*let routine g =
	let res = g in iter_vertex (v-> ) res;res;;
	
	sommet_a_traiter = liste_v res*)

let relier_pred g lpred noeud = 
	List.iter (fun v->add_edge g v noeud) lpred;;

let relier_succ g lsucc noeud =
	List.iter (fun v-> add_edge g noeud v) lsucc;; 

let routine g =
	let resultat = g in
	let l = liste_v resultat in
	List.iter (
		fun v-> 
			let su = succ g v and pr=pred g v and
                        na=DAG.Display.vertex_name v and
                        poid=Vertex.mass(V.label v) in
			let (premier,dernier) = prim resultat poid na in
				relier_succ resultat pr dernier;
                                relier_pred resultat su premier
	) l;
	resultat;;


(*faire cpie de g*)

(*recup nbr res, pred,succ*)
(*Appliquer pour chaque noeud prim*)
(*reconecter les pred et succ sur le resultat de *)

  
(* entrees: 
   - un nombre entier de ressources
   - un DAG
   sorties:
   - une trace d'execution du DAG 
   specifs: 
   - le DAG est suppose pondere (section 2.3)
   - les ressources sont supposees limitees 
   *)
(*
let ordonnanceur_graphe_pondere resDispo g =
  let rec iter y z res =
	match y with
	|[]-> res
	|_ -> let yordre = List.sort (fun a b -> let pa=prof_max a and pb=prof_max b in if pa>pb then 1 else if pa<pb then -1 else 0) y in 
			let (resetage,yfutur,newz) = etage_res_pond yordre z nbres g in iter yfutur newz res@[resetage]
  in iter (sans_dependance g) [] [];;
  
  
let etage_res_pond y z nbres g=
	let rec iter ycourant yfutur z resultat nbres = 
		match ycourant with
		|t::q -> 
			let poid = mass t in
				if(nbres-mass>=0) then
					let newz=t::z in
						let newy  = fold_succ (fun v l -> if(inclu (liste_pred v g) newz) then l@[v] else l) g t yfutur
					in iter q newy newz (resultat@[t]) (nbres-mass)
				else (resultat,yfutur@ycourant,z)
		|[] -> (resultat,yfutur,z)
	in iter y [] z [] nbres;;

*)

