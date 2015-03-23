(* fonction qui liste les sommets *)
(* liste_v: Digraph.t -> Vertex list *)
let liste_v g = (fold_vertex (fun v qt -> v::qt) 
                               g
                               [])
;;

let liste_edge g =
  fold_edges (fun u v l -> (u,v)::l) g [];; 

(*enlever liste_pred*)
let liste_pred v g =
  fold_pred (fun v l -> v::l ) g v [];;

(* entrees:-un DAG 
	sorties:liste des sommets sans dependances du graphe*)
let sans_dependance g =
  fold_vertex (fun v l -> if(in_degree g v = 0) then v::l else l) g [];; 

(* entrees:-un sommet v
			-une liste de sommets
	sortie:un booleen qui indique si v est dans l*)
let appartient v l = 
  List.fold_right (fun s b -> b||v=s) l false;;

(* entrees: -une liste de sommets ens1
			-une liste de sommets ens2
	sortie:un booleen qui indique si ens1 est inclu dans ens2*)
let inclu ens1 ens2 =
  List.fold_right (fun v b -> (appartient v ens2) && b) ens1 true;;

(* trace d'execution 
   definie en Section 2 de l'enonce (voir Figure 2)*)
type trace = (DAG.vertex list) list;;

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

(*******************************************************************)	
(*Effectue une etape passage de t à t+1
  entrees: y:une liste de taches à traiter en paralleles au temps t
		  z:la liste des taches terminés au temps t
		  g:le DAG
 sortie:(a,b,c): -a: la liste des taches validées durant le passage de t à t+1
				 -b:la liste des taches à traiter en paralleles pour le temps t+1
				 -c:la liste des taches terminees au temps t+1
*)
let etage y z g =
	let rec iter ycourant yfutur z res = 
		match ycourant with
		|t::q -> 
            let newz=t::z in 
            let newy  = fold_succ (fun v l -> if(inclu (liste_pred v g) newz) then l@[v] else l) g t yfutur
		    in iter q newy newz (res@[t])
		|[] -> (res,yfutur,z)
	in iter y [] z [];;
		
(* entrees: 
   - un DAG
   sorties:
   - une trace d'execution du DAG 
   specifs: 
   - le DAG est suppose non pondere
   - vous n'utiliserez pas d'heuristique
   *)		
let ordonnanceur_ressources_illimitees g =
  let rec iter y z res =
	match y with
	|[]-> res
	|_ -> let (resetage,yfutur,newz) = etage y z g in iter yfutur newz (res@[resetage])
  in iter (sans_dependance g) [] [];;
 
(*******************************************************************)	
(*Effectue une etape passage de t à t+1 en tenant compte d'un nombre de ressources limité
  entrees: y:une liste de taches à traiter en paralleles au temps t
		  z:la liste des taches terminés au temps t
		  nbres:nombre de ressources disponibles
		  g:le DAG
 sortie:(a,b,c): -a: la liste des taches validées durant le passage de t à t+1
				 -b:la liste des taches à traiter en paralleles pour le temps t+1
				 -c:la liste des taches terminees au temps t+1
*)
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


(*let prof_max2 v g=		
	let rec iter v g courant = fold_succ (fun v a-> max a (iter v g (courant+1))) g v 0 in iter v g 0;;
*)
	
(**************************************************************************************)	
	let max a b = if(a>=b) then a else b;;

(*Renvoit la longueur de la plus longue chaine partant de v dans get
 entree:un sommet v
		un DAG
 sortie:entier indiquant la profondeur max à partir de v dans g*)
let prof_max v g =
	let rec iter v g courant =
	let lsucc = succ g v in
		match lsucc with
		|[]->courant
		|_->List.fold_right (fun t l -> max l (iter t g (courant+1)) ) lsucc 0
	in iter v g 0;;
	
	
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

let ordonnanceur_ressources_limitees_avec_heuristique nbres g =
  let rec iter y z res =
	match y with
	|[]-> res
	|_ -> let yordre = List.sort (fun a b -> let pa=prof_max a g and pb=prof_max b g in if pa>pb then -1 else if pa<pb then 1 else 0) y in 
		  let (resetage,yfutur,newz) = etage_res yordre z nbres g 
		  in iter yfutur newz (res@[resetage])
  in iter (sans_dependance g) [] [];;
   

(****************************    ROUTINE      ******************************************)

(*creer un noeud de nom spécifié(nom) et l'ajoute au graphe(g)*)
let aux nom g =
	let a=V.create(nom,1) in add_vertex g a;a;;

(* Depondere l'arete (pred,succ) du DAG g en creant n taches paralleles avec
	n le ponderation de pred
	Pré: La transition entre pred et succ a deja etait supprime
 entree: -un DAG
		   -un noeud pred
		   -un noeud succ*)
let aux_routine g pred succ =
  let nom=fst(V.label pred) in
  let rec iter n =
    match n with
    |0-> ()
    |_-> let u=aux (nom^(string_of_int n)) g in
           add_edge g pred u;
           add_edge g u succ;
           iter (n-1)
  in iter (snd (V.label pred))
;;

(* Creation d'un DAG non pondere equivalent au DAG pondere fourni en entree
  entree :-un DAG pondere 
  sortie :-un nouveau DAG*)
let routine g =
	let resultat = copy g in
	let l = liste_edge resultat in
        List.iter (fun (u,v)->remove_edge resultat u v) l;
        List.iter (fun (u,v)->aux_routine resultat u v) l;
	    resultat;;


(**********************************************************************************)
   
(*entree:-un DAG
Marque chaque du noeud du graphe avec le nombre de ressources necessaires à la tache correspondante au noeud*)
let init_ordo g =
  iter_vertex (fun v -> Mark.set v (Vertex.mass(V.label v))) g;;

(*Effectue une etape passage de t à t+1 en tenant compte d'un nombre de ressources limité
  entrees: y:une liste de taches à traiter en paralleles au temps t
		  z:la liste des taches terminés au temps t
		  nbres:nombre de ressources disponibles
		  g:le DAG pondere
 sortie:(a,b,c): -a: la liste des taches validées durant le passage de t à t+1
				 -b:la liste des taches à traiter en paralleles pour le temps t+1
				 -c:la liste des taches terminees au temps t+1
*)
let etage_res_pond y z nbres g=
	let rec iter ycourant yfutur z resultat nbres = 
		match ycourant with
		|t::q -> 
			let poid = Mark.get t in
				if(nbres-poid>=0) then
					let newz=t::z in
					let newy  = fold_succ (fun v l -> if(inclu (liste_pred v g) newz) then l@[v] else l) g t yfutur
					in iter q newy newz (resultat@[t]) (nbres-poid)
				else if(nbres>0) then
                begin
                    Mark.set t (poid-nbres);
                    (resultat@[t],yfutur@ycourant,z)
                end
                else (resultat,yfutur@ycourant,z)
		|[] -> (resultat,yfutur,z)
	in iter y [] z [] nbres;;
	
(* entrees: 
   - un nombre entier de ressources
   - un DAG
   sorties:
   - une trace d'execution du DAG 
   specifs: 
   - le DAG est suppose pondere (section 2.3)
   - les ressources sont supposees limitees 
*)
let ordonnanceur_graphe_pondere resDispo g =
  init_ordo g;
  let rec iter y z res =
	match y with
	|[]-> res
	|_ -> let yordre = List.sort (fun a b -> let pa=prof_max a g and
        pb=prof_max b g in if pa>pb then -1 else if pa<pb then 1 else 0) y in 
		let (resetage,yfutur,newz) = etage_res_pond yordre z resDispo g
                in iter yfutur newz (res@[resetage])
  in iter (sans_dependance g) [] [];;

