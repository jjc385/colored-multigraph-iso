(* ::Package:: *)

<<IGraphM`


(* Expanded from code posted by Szabolcs on mma.se:  https://mathematica.stackexchange.com/a/97127/11035 *)
(* Extended to work if edge/vertex colors are already specified.
	Makes sure no edge colors are duplicated *)

ClearAll[myIGFindIsomorphismsNoDuplicates]
	
myIGFindIsomorphismsNoDuplicates[gr1_Graph|{gr1_Graph,opts1___},gr2_Graph|{gr2_Graph,opts2___},args___]:= (

	(* The original code fails if one graph is a multigraph and the other
		isn't.  To fix this, realize that such graphs will never be isomorphic
		and return early. *)
	If[ ! SameQ @@ MultigraphQ /@ {gr1, gr2}, Return@{} ]; (* return early if
		only one graph is a multigraph *)

	(* TODO -- assumes edges are undirected, but IGVF2 appears to support directed graphs *)
	Module[{colors1,colors2},
		colors1 = Counts[Sort/@EdgeList[gr1]];
		colors2 = Counts[Sort/@EdgeList[gr2]];

		If[ Length@Catenate[FilterRules[#,"EdgeColors"]& /@ {{opts1},{opts2}}]==0,	

			(* No special processing required *)
			IGraphM`IGVF2FindIsomorphisms[
				{Graph@Keys[colors1],"EdgeColors"->colors1, opts1},
				{Graph@Keys[colors2],"EdgeColors"->colors2, opts2}
			],

			(* properly merge options *)

(* 
			compositeColors1 =
			With[ { colorOpts1 = FilterRules[opts1,"EdgeColors"]},
				{ Lookup[colors1,#], multiLookup[colorOpts1, {#,Reverse@#}, 0] } &
					/@ Keys@colors1
			]
*)
			(* {{{ *)
			(* Make sure neither (1) color values nor (2) multigraph color keys (i.e., edges to be colored) are duplicated, for each graph*)
			(* 1 -- check color values *)
			Module[ {
				allMultiColors = Values /@ { colors1, colors2 } // Catenate,
				allOptsColors = Values@Lookup[#,"EdgeColors",{}]& /@ {{opts1},{opts2}} // Catenate
				},

				If[ Length @ Intersection[ allMultiColors, allOptsColors ] != 0,
					Throw[ "myIGFindIsomorphisms:  specified edge colors incompatible with multigraph colorings"]
				]
			];
			(* 2 -- check color keys (i.e., edges to be colored) *)
			Module[ {
				colorKeys1 = Map[Sort]@*Keys /@ { Select[colors1,#>1&], Lookup[{opts1}, "EdgeColors",{}] },
				colorKeys2 = Map[Sort]@*Keys /@ { Select[colors2,#>1&], Lookup[{opts2}, "EdgeColors",{}] }
				},

				If[ Length @ Intersection@@ colorKeys1 != 0,
					Throw[ "myIGFindIsomorphisms:  multigraph edges were assigned colors" ]
				]
			];
			(* }}} *)

			(* now that colors have been shown to be compatible, attempt to combine them *)
			Module[{newColors1, newColors2},
				newColors1 = 
					Append[ colors1, 
						KeyMap[Sort]@Association@Lookup[{opts1},"EdgeColors"]
					];
				newColors2 = 
					Append[ colors2, 
						KeyMap[Sort]@Association@Lookup[{opts2},"EdgeColors"]
					];
										


				IGraphM`IGVF2FindIsomorphisms[
					{Graph@Keys[colors1],"EdgeColors"->newColors1, opts1},
					{Graph@Keys[colors2],"EdgeColors"->newColors2, opts2},
					args
				]
			]
		]


	]
)
