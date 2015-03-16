(*
Cree les graphes de test dag1 ... dag5 et genere les fichiers .dot associes.
Pour visualiser les graphes : 
	dot dag.dot -Tps -o dag.ps
	evince dag.ps
*)

module Vertex = struct
  type t = string*int
  let compare : t -> t -> int = Pervasives.compare
  let hash = Hashtbl.hash
  let equal = (=)
  let default = (0,0)
  let name (nod : string*int) = fst nod
  let mass (nod : string*int) = snd nod
  let strname (nod : string*int) = name nod
  let strmass (nod : string*int) = string_of_int (mass nod)
end

module Edge = struct
  type t = int
  let compare : t -> t -> int = Pervasives.compare
  let hash = Hashtbl.hash
  let equal = (=)
  let default = 0
end

module DAG = 
struct
	include Graph.Imperative.Digraph.AbstractLabeled(Vertex)(Edge)
	
	module Display = struct
		include Graph.Imperative.Digraph.AbstractLabeled(Vertex)(Edge)
		let vertex_name v = Vertex.strname (V.label v)
		let graph_attributes _ = []
		let default_vertex_attributes _ = []
		let vertex_attributes v = [`Label ((Vertex.strname (V.label v))^":"^(Vertex.strmass (V.label v)))]
		let default_edge_attributes _ = []
		let edge_attributes e = []
		let get_subgraph _ = None
	end
	module Dot_ = Graph.Graphviz.Dot(Display)
	module Neato = Graph.Graphviz.Neato(Display)

	let dot_output g f =
		let oc = open_out f in
		if is_directed then Dot_.output_graph oc g else Neato.output_graph oc g;
		close_out oc

end 

open DAG

let dag1 = create();;

let vb1 = V.create("b",1);;
let vc1 = V.create("c",1);;
let vd1 = V.create("d",1);;
let ve1 = V.create("e",1);;
let vf1 = V.create("f",1);;
let vg1 = V.create("g",1);;
let vh1 = V.create("h",1);;
let vi1 = V.create("i",1);;
let vj1 = V.create("j",1);;
let vk1 = V.create("k",1);;
let vl1 = V.create("l",1);;
let vm1 = V.create("m",1);;
let vn1 = V.create("n",1);;
let vo1 = V.create("o",1);;
let vp1 = V.create("p",1);;
let vq1 = V.create("q",1);;
let vr1 = V.create("r",1);;
let vs1 = V.create("s",1);;


add_vertex dag1 vb1;;
add_vertex dag1 vc1;;
add_vertex dag1 vd1;;
add_vertex dag1 ve1;;
add_vertex dag1 vf1;;
add_vertex dag1 vg1;;
add_vertex dag1 vh1;;
add_vertex dag1 vi1;;
add_vertex dag1 vj1;;
add_vertex dag1 vk1;;
add_vertex dag1 vl1;;
add_vertex dag1 vm1;;
add_vertex dag1 vn1;;
add_vertex dag1 vo1;;
add_vertex dag1 vp1;;
add_vertex dag1 vq1;;
add_vertex dag1 vr1;;
add_vertex dag1 vs1;;


add_edge dag1 vs1 vk1;;
add_edge dag1 vs1 vp1;;
add_edge dag1 vj1 vi1;;
add_edge dag1 vp1 vh1;;
add_edge dag1 vg1 vh1;;
add_edge dag1 vh1 vc1;;
add_edge dag1 vp1 vg1;;
add_edge dag1 vp1 vi1;;
add_edge dag1 vf1 vo1;;
add_edge dag1 vi1 vd1;;
add_edge dag1 vi1 vf1;;
add_edge dag1 vd1 vl1;;
add_edge dag1 vd1 ve1;;
add_edge dag1 vd1 vm1;;
add_edge dag1 vb1 vl1;;
add_edge dag1 vn1 vm1;;
add_edge dag1 ve1 vr1;;
add_edge dag1 vq1 vr1;;

dot_output dag1 "dag1.dot";;

let dag2 = create();;

let vx2 = V.create("x",1);;
let vb2 = V.create("b",1);;
let vc2 = V.create("c",1);;
let vo2 = V.create("o",1);;
let ve2 = V.create("e",1);;
let vf2 = V.create("f",1);;
let vi2 = V.create("i",1);;
let vh2 = V.create("h",1);;
let vr2 = V.create("r",1);;
let vj2 = V.create("j",1);;
let va2 = V.create("a",1);;
let vn2 = V.create("n",1);;

add_vertex dag2 vx2;;
add_vertex dag2 vb2;;
add_vertex dag2 vc2;;
add_vertex dag2 vo2;;
add_vertex dag2 ve2;;
add_vertex dag2 vf2;;
add_vertex dag2 vi2;;
add_vertex dag2 vh2;;
add_vertex dag2 vr2;;
add_vertex dag2 vj2;;
add_vertex dag2 va2;;
add_vertex dag2 vn2;;

add_edge dag2 va2 vj2;;
add_edge dag2 va2 vn2;;
add_edge dag2 vj2 vf2;;
add_edge dag2 vn2 vo2;;
add_edge dag2 vn2 vr2;;
add_edge dag2 vo2 vr2;;
add_edge dag2 vo2 ve2;;
add_edge dag2 vr2 vf2;;
add_edge dag2 ve2 vh2;;
add_edge dag2 vr2 ve2;;
add_edge dag2 ve2 vx2;;
add_edge dag2 vi2 vb2;;
add_edge dag2 vi2 vc2;;
add_edge dag2 vx2 vi2;;

dot_output dag2 "dag2.dot";;

let dag3 = create();;

let va3 = V.create("a",1);;
let vv3 = V.create("v",1);;
let vc3 = V.create("c",1);;
let vd3 = V.create("d",1);;
let ve3 = V.create("e",1);;
let vf3 = V.create("f",1);;
let vi3 = V.create("i",1);;
let vh3 = V.create("h",1);;
let vg3 = V.create("g",1);;
let vj3 = V.create("j",1);;
let vm3 = V.create("m",1);;
let vn3 = V.create("n",1);;
let vk3 = V.create("k",1);;
let vl3 = V.create("l",1);;

add_vertex dag3 va3;;
add_vertex dag3 vv3;;
add_vertex dag3 vc3;;
add_vertex dag3 vd3;;
add_vertex dag3 ve3;;
add_vertex dag3 vf3;;
add_vertex dag3 vg3;;
add_vertex dag3 vh3;;
add_vertex dag3 vi3;;
add_vertex dag3 vj3;;
add_vertex dag3 vk3;;
add_vertex dag3 vl3;;
add_vertex dag3 vm3;;
add_vertex dag3 vn3;;

add_edge dag3 vg3 vf3;;
add_edge dag3 vn3 vf3;;
add_edge dag3 vn3 va3;;
add_edge dag3 vd3 va3;;
add_edge dag3 vd3 vl3;;
add_edge dag3 vj3 vl3;;
add_edge dag3 vj3 vm3;;
add_edge dag3 vk3 vm3;;
add_edge dag3 vf3 vc3;;
add_edge dag3 va3 vc3;;
add_edge dag3 va3 vv3;;
add_edge dag3 vl3 vv3;;
add_edge dag3 vl3 ve3;;
add_edge dag3 vm3 ve3;;
add_edge dag3 vc3 vi3;;
add_edge dag3 vv3 vi3;;
add_edge dag3 vv3 vh3;;
add_edge dag3 ve3 vh3;;

dot_output dag3 "dag3.dot";;


let dag4 = create();;

let va4 = V.create("a",4);;
let vb4 = V.create("b",17);;
let vc4 = V.create("c",13);;
let vd4 = V.create("d",17);;
let ve4 = V.create("e",11);;
let vf4 = V.create("f",9);;
let vi4 = V.create("i",4);;
let vh4 = V.create("h",1);;
let vg4 = V.create("g",10);;
let vj4 = V.create("j",8);;
let vt4 = V.create("t",15);;
let vl4 = V.create("l",5);;

add_vertex dag4 va4;;
add_vertex dag4 vb4;;
add_vertex dag4 vc4;;
add_vertex dag4 vd4;;
add_vertex dag4 ve4;;
add_vertex dag4 vf4;;
add_vertex dag4 vg4;;
add_vertex dag4 vh4;;
add_vertex dag4 vi4;;
add_vertex dag4 vj4;;
add_vertex dag4 vt4;;
add_vertex dag4 vl4;;

add_edge dag4 vt4 va4;;
add_edge dag4 vd4 va4;;
add_edge dag4 vb4 vj4;;
add_edge dag4 vd4 vi4;;
add_edge dag4 vd4 vf4;;
add_edge dag4 va4 vi4;;
add_edge dag4 va4 ve4;;
add_edge dag4 va4 vg4;;
add_edge dag4 vj4 vc4;;
add_edge dag4 vf4 ve4;;
add_edge dag4 vf4 vg4;;
add_edge dag4 vc4 vh4;;
add_edge dag4 vi4 vh4;;
add_edge dag4 ve4 vl4;;
add_edge dag4 vg4 vl4;;

dot_output dag4 "dag4.dot";;

let dag5 = create();;

let va5 = V.create("a",42);;
let vb5 = V.create("b",171);;
let vc5 = V.create("c",131);;
let vd5 = V.create("d",171);;
let ve5 = V.create("e",111);;
let vf5 = V.create("f",91);;
let vi5 = V.create("i",42);;
let vh5 = V.create("h",11);;
let vg5 = V.create("g",101);;
let vj5 = V.create("j",81);;
let vt5 = V.create("t",151);;
let vl5 = V.create("l",51);;

add_vertex dag5 va5;;
add_vertex dag5 vb5;;
add_vertex dag5 vc5;;
add_vertex dag5 vd5;;
add_vertex dag5 ve5;;
add_vertex dag5 vf5;;
add_vertex dag5 vg5;;
add_vertex dag5 vh5;;
add_vertex dag5 vi5;;
add_vertex dag5 vj5;;
add_vertex dag5 vt5;;
add_vertex dag5 vl5;;

add_edge dag5 vt5 va5;;
add_edge dag5 vd5 va5;;
add_edge dag5 vb5 vj5;;
add_edge dag5 vd5 vi5;;
add_edge dag5 vd5 vf5;;
add_edge dag5 va5 vi5;;
add_edge dag5 va5 ve5;;
add_edge dag5 va5 vg5;;
add_edge dag5 vj5 vc5;;
add_edge dag5 vf5 ve5;;
add_edge dag5 vf5 vg5;;
add_edge dag5 vc5 vh5;;
add_edge dag5 vi5 vh5;;
add_edge dag5 ve5 vl5;;
add_edge dag5 vg5 vl5;;

dot_output dag5 "dag5.dot";;






