import DAG.SearchCore

open DAG.SearchCore

namespace DAG

def sampleNames : Array String := #[
  "Test.Foo.alpha",
  "Test.Bar.beta",
  "DAG.SearchRank.searchEnv",
  "Socratic.Core"
]

example : containsCI "Test.Foo.alpha" "foo" = true := sorry

example : containsCI "Test.Foo.alpha" "zzz" = false := sorry

example :
    queryContains sampleNames "Test" =
      #["Test.Foo.alpha", "Test.Bar.beta"] := sorry

example :
    queryContainsCI sampleNames "test" =
      #["Test.Foo.alpha", "Test.Bar.beta"] := sorry

example : (queryContainsWithCount sampleNames "search").2 = 1 := sorry

example : (queryContainsWithCount sampleNames "missing").1 = #[] := sorry

end DAG
