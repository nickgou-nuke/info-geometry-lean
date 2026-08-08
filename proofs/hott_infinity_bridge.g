repositorySourceCount:=8;; mathlibSourceCount:=1;; totalSourceCount:=9;; bridgeLayerCount:=9;; compatibilityEdgeCount:=11;; hottBridgeRank:=29;;
homotopyEquivFields:=4;; exactCoupleMaps:=3;; serrePageStart:=2;; serreStablePage:=3;; quasicategorySimplexArity:=2;; modelCategoryClasses:=3;; fibredProjectionCount:=1;; infinityBridgeSignature:=18;;
if repositorySourceCount<>8 or mathlibSourceCount<>1 or totalSourceCount<>9 or bridgeLayerCount<>9 or compatibilityEdgeCount<>11 or hottBridgeRank<>29 then Error("counts"); fi;
if homotopyEquivFields<>4 or exactCoupleMaps<>3 or serrePageStart<>2 or serreStablePage<>3 or quasicategorySimplexArity<>2 or modelCategoryClasses<>3 or fibredProjectionCount<>1 or infinityBridgeSignature<>18 then Error("signature"); fi;
edges:=[[1,2],[2,3],[3,4],[4,5],[6,4],[6,5],[7,6],[8,7],[9,8],[9,5],[5,2]];;
if Length(edges)<>11 then Error("graph edges"); fi;
Print(rec(repositorySourceCount:=repositorySourceCount,mathlibSourceCount:=mathlibSourceCount,totalSourceCount:=totalSourceCount,bridgeLayerCount:=bridgeLayerCount,compatibilityEdgeCount:=compatibilityEdgeCount,hottBridgeRank:=hottBridgeRank,homotopyEquivFields:=homotopyEquivFields,exactCoupleMaps:=exactCoupleMaps,serrePageStart:=serrePageStart,serreStablePage:=serreStablePage,quasicategorySimplexArity:=quasicategorySimplexArity,modelCategoryClasses:=modelCategoryClasses,fibredProjectionCount:=fibredProjectionCount,infinityBridgeSignature:=infinityBridgeSignature,graphEdges:=Length(edges),d2Target:=[2,0],d2Square:=0),"\n");
QUIT;
