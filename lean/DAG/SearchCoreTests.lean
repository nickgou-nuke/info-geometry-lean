import DAG.SearchCore

open DAG.SearchCore

namespace DAG

def sampleNames : Array String := #[
  "InfoGeometry.Foo.alpha",
  "InfoGeometry.Bar.beta",
  "DAG.SearchRank.searchEnv",
  "Socratic.Core"
]

example : containsCI "InfoGeometry.Foo.alpha" "foo" = true := by
  native_decide

example : containsCI "InfoGeometry.Foo.alpha" "zzz" = false := by
  native_decide

example :
    queryContains sampleNames "InfoGeometry" =
      #["InfoGeometry.Foo.alpha", "InfoGeometry.Bar.beta"] := by
  native_decide

example :
    queryContainsCI sampleNames "infogeometry" =
      #["InfoGeometry.Foo.alpha", "InfoGeometry.Bar.beta"] := by
  native_decide

example : (queryContainsWithCount sampleNames "search").2 = 1 := by
  native_decide

example : (queryContainsWithCount sampleNames "missing").1 = #[] := by
  native_decide

end DAG
