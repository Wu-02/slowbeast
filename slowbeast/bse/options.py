from slowbeast.cfkind import KindSEOptions


class BSELFOptions(KindSEOptions):
    def __init__(self, copyopts=None) -> None:
        super().__init__(copyopts)
        if not isinstance(copyopts, BSELFOptions):
            # those are other options to copy, copied in the super classes, not here
            copyopts = None

        if copyopts:
            self.fold_loops = copyopts.fold_loops
            self.target_is_whole_seq = copyopts.target_is_whole_seq
            self.union_abstractions = copyopts.union_abstractions
            self.union_extensions = copyopts.union_extensions
            self.union_matched = copyopts.union_matched
            self.add_unwind_invariants = copyopts.add_unwind_invariants
        else:
            self.fold_loops = True
            self.target_is_whole_seq = True
            self.union_abstractions = False
            self.union_extensions_threshold = None
            self.union_matched = True
            self.add_unwind_invariants = False
