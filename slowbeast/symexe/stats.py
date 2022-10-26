class SEStats:
    def __init__(self) -> None:
        # all paths (including ones that hit an error or terminated early)
        self.paths = 0
        # paths that exited (the state is exited)
        self.exited_paths = 0
        self.killed_paths = 0
        self.terminated_paths = 0
        self.errors = 0

    def add(self, rhs) -> None:
        self.paths = rhs.paths
        self.exited_paths = rhs.exited_paths
        self.killed_paths = rhs.killed_paths
        self.terminated_paths = rhs.terminated_paths
        self.errors = rhs.errors
