(* ::Package:: *)

(* ::Section:: *)
(*Setup*)


(* ::Subsection:: *)
(*OP's `decorateGraph` function (modified)*)


ClearAll[decorateGraph]
decorateGraph[con_, vrts_:<||>, edgs_] := Module[{g, gv},
  g = Graph[con];
  gv = Fold[SetProperty[{#1, #2}, 
  {VertexStyle -> ColorData[60, vrts[[Key[#2]]] ], VertexSize -> Medium}] &, g, 
    Keys[vrts]];
  Fold[SetProperty[{#1, #2}, 
     EdgeStyle -> {ColorData[60, edgs[[Key[#2]]]], Thick}] &, gv, 
   Keys[edgs]]
  ]
  
decorateGraph[{g_, opts___?(MatchQ[_String->_Association])}]:=Module[ {first},
	first = Last@First[ #, ""-><||> ]& ;
	decorateGraph[ g, first@FilterRules[{opts},"VertexColors"], first@FilterRules[{opts},"EdgeColors"] ]
	]


(* ::Section:: *)
(*Tests*)


(* ::Subsection:: *)
(*Assert Machinery*)


(* set up linked list of assert results *)
assertRes={};

ClearAll[assert]
assert[ expr_ ]:= (assertRes={assertRes, expr}; expr)


(* ::Subsection:: *)
(*Testing setup *)


SetOptions[Graph,VertexLabels->Automatic];


gSquare=CycleGraph[4,VertexLabels->Automatic];
gSquareHSplit2=Graph[VertexList@gSquare,{EdgeList@gSquare, {multiEdgeH=1<->3,1<->3}}//Catenate]
gSquareVSplit2=Graph[VertexList@gSquare,{EdgeList@gSquare, {multiEdgeV=2<->4,2<->4}}//Catenate]


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


(* ::Subsubsection::Closed:: *)
(*Both:  simple edge colored the same*)


myIGFindIsomorphisms[
	{gSquareHSplit2,"EdgeColors"-><|(1<->2)->1|>},
	{gSquareVSplit2,"EdgeColors"-><|(1<->2)->1|>}
]
Length@%>0
assertRes = {assertRes, %};


(* ::Subsubsection:: *)
(*Both:  single-colored multi-edge *)


{
	{gSquareHSplit2,"EdgeColors"-><|multiEdgeH->2|>},
	{gSquareVSplit2,"EdgeColors"-><|multiEdgeV->2|>}
};
decorateGraph/@%
%%;
myIGFindIsomorphisms@@%
Length@%>0 // assert



{
	{gSquareHSplit2,"EdgeColors"-><|multiEdgeH->2|>},
	{gSquareVSplit2,"EdgeColors"-><|multiEdgeV->3|>}
};
decorateGraph/@%
%%;
myIGFindIsomorphisms@@%
Length@% == 0 // assert


(* ::Subsubsection:: *)
(*Both:  multi-colored multi-edge *)


{
	{gSquareHSplit2,"EdgeColors"-><|multiEdgeH->{1,2}|>},
	{gSquareVSplit2,"EdgeColors"-><|multiEdgeV->{1,2}|>}
};
(*decorateGraph/@%
%%;*)
myIGFindIsomorphisms@@%
Length@% > 0 // assert


{
	{gSquareHSplit2,"EdgeColors"-><|multiEdgeH->{1,2}|>},
	{gSquareVSplit2,"EdgeColors"-><|multiEdgeV->{2,1}|>}
};
(*decorateGraph/@%
%%;*)
myIGFindIsomorphisms@@%
Length@% > 0 // assert


{
	{gSquareHSplit2,"EdgeColors"-><|multiEdgeH->{1,2}|>},
	{gSquareVSplit2,"EdgeColors"-><|multiEdgeV->{3,4}|>}
};
(*decorateGraph/@%
%%;*)
myIGFindIsomorphisms@@%
Length@% == 0 // assert


{
	{gSquareHSplit2,"EdgeColors"-><|multiEdgeH->{1,2}|>},
	{gSquareVSplit2,"EdgeColors"-><|multiEdgeV->{2}|>}
};
(*decorateGraph/@%
%%;*)
myIGFindIsomorphisms@@%
Length@% == 0 // assert


{
	{gSquareHSplit2,"EdgeColors"-><|multiEdgeH->{1,2}|>},
	{gSquareVSplit2,"EdgeColors"-><|multiEdgeV->{1,2,3}|>}
};
(*decorateGraph/@%
%%;*)
myIGFindIsomorphisms@@%
Length@% == 0 // assert


(* ::Subsubsection:: *)
(*1-cycles*)



{gSquareHSplit2, gSquareVSplit2};
{#1->multiEdgeH,#2->multiEdgeV}& @@%;
Graph[Append[EdgeList@#1,First@#2<->First@#2]]&@@@%;

{
	{#1,"EdgeColors"-><|multiEdgeH->{1,2}, (First@multiEdgeH<->First@multiEdgeH) -> 4|>},
	{#2,"EdgeColors"-><|multiEdgeV->{1,2}, (First@multiEdgeV<->First@multiEdgeV) -> 4|>}
} & @@ %;

myIGFindIsomorphisms@@%
Length@% > 0 //assert


{gSquareHSplit2, gSquareVSplit2};
{#1->multiEdgeH,#2->multiEdgeV}& @@%;
Graph[Join[EdgeList@#1,{First@#2<->First@#2,First@#2<->First@#2}]]&@@@%;

{
	{#1,"EdgeColors"-><|multiEdgeH->{1,2}, (First@multiEdgeH<->First@multiEdgeH) -> 4|>},
	{#2,"EdgeColors"-><|multiEdgeV->{1,2}, (First@multiEdgeV<->First@multiEdgeV) -> 4|>}
} & @@ %;

myIGFindIsomorphisms@@%
Length@% > 0 //assert


{gSquareHSplit2, gSquareVSplit2};
{#1->multiEdgeH,#2->multiEdgeV}& @@%;
Graph[Join[EdgeList@#1,{First@#2<->First@#2,First@#2<->First@#2}]]&@@@%;

{
	{#1,"EdgeColors"-><|multiEdgeH->{1,2}, (First@multiEdgeH<->First@multiEdgeH) -> {4,5}|>},
	{#2,"EdgeColors"-><|multiEdgeV->{1,2}, (First@multiEdgeV<->First@multiEdgeV) -> {4,5}|>}
} & @@ %;

myIGFindIsomorphisms@@%
Length@% > 0 //assert


{gSquareHSplit2, gSquareVSplit2};
{#1->multiEdgeH,#2->multiEdgeV}& @@%;
Graph[Join[EdgeList@#1,{First@#2<->First@#2,First@#2<->First@#2}]]&@@@%;

{
	{#1,"EdgeColors"-><|multiEdgeH->{1,2}, (First@multiEdgeH<->First@multiEdgeH) -> {5,4}|>},
	{#2,"EdgeColors"-><|multiEdgeV->{1,2}, (First@multiEdgeV<->First@multiEdgeV) -> {4,5}|>}
} & @@ %;

myIGFindIsomorphisms@@%
Length@% > 0 //assert


{gSquareHSplit2, gSquareVSplit2};
{#1->multiEdgeH,#2->multiEdgeV}& @@%;
Graph[Join[EdgeList@#1,{First@#2<->First@#2,First@#2<->First@#2}]]&@@@%;

{
	{#1,"EdgeColors"-><|multiEdgeH->{1,2}, (First@multiEdgeH<->First@multiEdgeH) -> {4,5}|>},
	{#2,"EdgeColors"-><|multiEdgeV->{1,2}, (First@multiEdgeV<->First@multiEdgeV) -> {4,6}|>}
} & @@ %;

myIGFindIsomorphisms@@%
Length@% == 0 //assert


(* ::Subsubsection:: *)
(*OP's tests*)


gr[1]={1 <-> 2, 3 <-> 8, 8 <-> 9, 9 <-> 4, 1 <-> 10, 10 <-> 11, 11 <-> 2, 5 <-> 5, 5 <-> 6, 3 <-> 6, 6 <-> 7, 4 <-> 7, 5 <-> 7}
vr[1]=<|8 -> 3, 10 -> 3, 9 -> 7, 11 -> 7|>
ed[1]=<|6 <-> 7 -> 10|>

gr[2]={1 <-> 2, 3 <-> 8, 8 <-> 9, 9 <-> 3, 4 <-> 10, 10 <-> 11, 11 <-> 2, 5 <-> 5, 3 <-> 3, 5 <-> 6, 5 <-> 6, 6 <-> 7, 1 <-> 7, 4 <-> 7}
vr[2]=<|8 -> 3, 10 -> 3, 9 -> 7, 11 -> 7|>
ed[2]=<|6 <-> 7 -> 10|>




GraphicsRow[
{decorateGraph[Graph[gr[1]], vr[1], ed[1]],
 decorateGraph[Graph[gr[2]], vr[2], ed[2]]}, 
   Dividers -> Center, FrameStyle -> Directive[Dashed, Blue]]


myIGFindIsomorphisms[{Graph[gr[1]], "VertexColors" -> vr[1], "EdgeColors" -> ed[1]}, {Graph[gr[2]], "VertexColors" -> vr[2], "EdgeColors" -> ed[2]}]


(* ::Subsection:: *)
(*Make sure asserts are all True*)


assertRes = {assertRes,True};
(
And @@ Flatten@assertRes
  // If[ ! TrueQ@#, Throw["Asserts failed"], Print["Asserts passed"] ]&
)
