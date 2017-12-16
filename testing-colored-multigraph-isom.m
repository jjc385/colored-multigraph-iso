(* ::Package:: *)

(* ::Section:: *)
(*Tests*)


(* ::Subsection:: *)
(*Assert Machinery*)


(* set up linked list of assert results *)
assertRes={};


(* ::Subsection::Closed:: *)
(*Testing setup *)


SetOptions[Graph,VertexLabels->Automatic];


gSquare=CycleGraph[4,VertexLabels->Automatic];
gSquareHSplit2=Graph[VertexList@gSquare,{EdgeList@gSquare, {1<->3,1<->3}}//Catenate]
gSquareVSplit2=Graph[VertexList@gSquare,{EdgeList@gSquare, {2<->4,2<->4}}//Catenate]


(* ::Subsection:: *)
(*Tests (asserts)*)


(* ::Subsubsection::Closed:: *)
(*No edge colors (multigraphs)*)


myIGFindIsomorphisms[gSquareHSplit2,gSquareVSplit2]
Length@%>0
assertRes = {assertRes, %};


myIGFindIsomorphisms[{gSquareHSplit2},gSquareVSplit2]
Length@%>0
assertRes = {assertRes, %};


myIGFindIsomorphisms[gSquareHSplit2,{gSquareVSplit2}]
Length@%>0
assertRes = {assertRes, %};


myIGFindIsomorphisms[{gSquareHSplit2},{gSquareVSplit2}]
Length@%>0
assertRes = {assertRes, %};


(* ::Subsubsection:: *)
(*Both:  simple edge colored the same*)


myIGFindIsomorphisms[
	{gSquareHSplit2,"EdgeColors"-><|(1->2)->1|>},
	{gSquareVSplit2,"EdgeColors"-><|(1->2)->1|>}
]//reapRule["debug"->_]
Last@%
%%;
First@%;
Length@%>0
assertRes = {assertRes, %};


(* ::Subsection:: *)
(*Make sure asserts are all True*)


assertRes = {assertRes,True};
(
And @@ Flatten@assertRes
  // If[ ! TrueQ@#, Throw["Asserts failed"], Print["Asserts passed"] ]&
)
