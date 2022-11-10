from slowbeast.symexe.statesset import StatesSet


class InductiveSetsTree:
    class Node:
        def __init__(self, statesset, successor):
            self.iset = statesset
            self.successor = successor
            self.predecessors = []
            if successor:
                successor.predecessors.append(self)

    def __init__(self, root: StatesSet):
        self.root = InductiveSetsTree.Node(root, successor=None)
        self.frontiers = {self.root}
        self.all_states = root.copy()

    def add_set(self, iset, successor: Node):
        """
        Add a new set that was created as a (overapproximated) pre-image
        of some set in the frontiers.

        NOTE that the methods take only references to the objects,
        so do a copy if you plan to modify the objects later.
        """
        nd = InductiveSetsTree.Node(iset, successor)

        frontiers = self.frontiers
        if successor in frontiers:
            frontiers.remove(successor)
        else:
            assert len(successor.predecessors) > 0

        frontiers.add(nd)
        self.all_states.add(iset).rewrite_and_simplify()
