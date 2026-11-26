import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.UndirectedNetworkCodingLiLi

/-- The Li–Li Conjecture (2004): for every finite undirected multiple-unicast network with
    distinct source–destination pairs, symmetric network coding throughput equals fractional
    multicommodity routing throughput. -/
def Statement : Prop :=
  ∀ (n : ℕ) (net : UndirectedMultipleUnicast (Fin n)),
    0 < net.numPairs →
    (∀ i : Fin net.numPairs, net.src i ≠ net.dst i) →
    undirectedCodingThroughput net = undirectedRoutingThroughput net

def problem : OpenProblem where
  id := "undirected-network-coding-li-li"
  title := "The Li–Li Conjecture for Undirected Multiple-Unicast Network Coding"
  category := .networkCoding
  status := .open
  posedBy := "Zongpeng Li and Baochun Li"
  posedYear := 2004
  statement := Statement

end InfoTheory.Problems.UndirectedNetworkCodingLiLi
