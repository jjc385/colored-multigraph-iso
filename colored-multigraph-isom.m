(* ::Package:: *)

<<jjcLib`


(* ::Section:: *)
(*Implementation*)


<<IGraphM`


(* ::Subsection::Closed:: *)
(*My old, hacky implementation*)


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


(* ::Subsection:: *)
(*Better implementation*)


(* Expanded from code posted by Szabolcs on mma.se:  https://mathematica.stackexchange.com/a/97127/11035 *)
(* Extended to work if edge/vertex colors are already specified.
	Makes sure no edge colors are duplicated *)

ClearAll[myIGFindIsomorphisms]
	
myIGFindIsomorphisms[gr1_Graph|{gr1_Graph,opts1___},gr2_Graph|{gr2_Graph,opts2___},args___]:= (

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

			(* ** properly merge options ** *)
			
			Module[ { allMultiColors, allOptsColors, allColorPairs, 
					colorPairsToIntAssoc, nColors,
					newColors1, newColors2 },
				allMultiColors = { colors1, colors2 } ;
				allOptsColors = Lookup[#,"EdgeColors",<||>]& /@ {{opts1},{opts2}} ;
				
				( allOptsColors // Sow[ #, "debug" -> "allOptsColors" ] & );
				
				(* process optsColors into association form *)
				
				allOptsColors = MapIndexed[
					With[{ g = Extract[ {gr1, gr2}, #2 ] },
						Switch[ #, 
							None|Null, <||>,
							_List, Thread[ EdgeList@g -> # ],
							_Association, #,
							_, Throw@StringForm["EdgeColor option not of the correct form:  ``",#]
						]
					] & ,
					allOptsColors
				];
				
				Throw@StringForm[ "allOptsColors:  `1` \n allMultiColors:   `2`", allOptsColors, allMultiColors];
				
				(* sort edges in allOptsColors *)
				allOptsColors = KeyValueMap[ Sort@#1 -> #2 & ] /@ allOptsColors
				 (* ensure there are no duplicate edges upon sorting *)
				 // Map[ With[ {prev=#}, 
				        Association@# 
				         // If[ Length@# != Length@prev, 
				                Throw@StringForm["Unimplemented:  color options specified for edge in both directions.\n  prev:  `1`\n new:  `2`",prev,#] 
				            ]&
				    ] & ];
				
				Throw@StringForm[ "allOptsColors:  `1` \n allMultiColors:   `2`", allOptsColors, allMultiColors];

				(* first, rewrite edge 'colors' in the form {optColor, multiColor} *)
				allColorPairs = ( 
					Transpose@ { allOptsColors, allMultiColors }
					 // Map[ KeyUnion[ #, 0& ] & /* Merge[ Identity ] ] (* { <|edge1i\[Rule]{optColor1i,multiColor1i}, ...|>, <|edge2i\[Rule]{,},...|> } *)
					 // Sow[ #, "debug"->"allColorLists" ] & 
				);
				
				(* now convert the {optColor, multiColor} pairs to unique integers *)
				
				colorPairsToIntAssoc = <||>;
				nColors=0;
				
				 (
					allColorPairs 
					 // Map[ Values ]
					 // Catenate            (* { {optC1, multiC1}, ... } *)
					 (* // Sort *)          (* Sort color pairs, if desired *)
					 // Scan[
					        If[ !KeyExistsQ[ colorPairsToIntAssoc, # ],
					            AssociateTo[ colorPairsToIntAssoc, # -> ++nColors ]
					        ] &
					    ]
				);
				
				(colorPairsToIntAssoc // Sow[ #, "debug"->"colorPairsToIntAssoc" ] & );
				
				(*
				(* doesn't work -- mixed edges from different graphs *)
				
				(* associate edges according to colors *)
				colorPairKeysAssoc = (
					allColorPairs
					 // Map[ MapAt[List, -1] @* Map[Reverse] @* Normal ]  
					 // Catenate          (* { color_i \[Rule] {edge_i}, ... } *)
					 // Merge[ Catenate ] (* <| color_i \[Rule] { edge_1, edge_2, ...}, ... |> *)
				 ) ;*)
				 
				{newColors1, newColors2} = (
					Map[ Replace[colorPairsToIntAssoc], allColorPairs, {2} ]
					// Sow[ #, "debug"->"allNewColors" ] & ;
				);					


				IGraphM`IGVF2FindIsomorphisms[
					{Graph@Keys[colors1],"EdgeColors"->newColors1, Sequence@@FilterRules[{opts1},Except@"EdgeColors"]},
					{Graph@Keys[colors2],"EdgeColors"->newColors2, Sequence@@FilterRules[{opts2},Except@"EdgeColors"]},
					args
				]
				
			]
		
		]


	]
)
