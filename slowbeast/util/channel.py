import os
from time import sleep
from queue import Queue

from slowbeast.util.debugging import dbg, dbgv

READ_BUF_SIZE = 1024


class Channel:
    """
    Uni-directional channel between two processes.
    """

    def __init__(self, descr):
        # for now we always assume pipes
        method = "pipe"
        mode, path = descr.split(":")
        assert mode in ("w", "r"), mode

        self._chan = None
        self._method = method
        self._im_producer = mode == "w"
        self._path = path

        if self._im_producer:
            os.mkfifo(self._path)
            # remember -- this will block until the reader creates the channel
            n = 0
            while n < 10:
                try:
                    self._chan = os.open(self._path, os.O_WRONLY | os.O_NONBLOCK)
                except OSError as e:
                    sleep(0.300)
                    dbgv(f"Waiting for channel {self._path} (I'm producer)")
                n += 1
            if self._chan is None:
                dbg(f"Failed waiting for channel {self._path} (I'm producer)")
            
        else:
            n = 0
            while n < 10:
                try:
                    self._chan = os.open(self._path, os.O_RDONLY | os.O_NONBLOCK)
                except FileNotFoundError as e:
                    sleep(0.300)
                    dbgv(f"Waiting for channel {self._path} (I'm reader)")
                n += 1
            if self._chan is None:
                dbg(f"Failed waiting for channel {self._path} (I'm reader)")

        self._unfinished_line = None
        self._lines = Queue()

    def recv(self):
        assert not self._im_producer, "Producer is receiving"

        if self._chan is None:
            return None

        if not self._lines.empty():
            return self._lines.get()

        try:
            buf = os.read(self._chan, READ_BUF_SIZE)
        except BlockingIOError:  # temporarily unavailable
            buf = None

        if not buf:  # buf = None or ""
            return None

        lines = buf.split(b"\n")
        if self._unfinished_line is not None:
            lines[0] = self._unfinished_line + lines[0]
        if buf[-1] == "\n":
            self._unfinished_line = None
        else:
            self._unfinished_line = lines[-1]
            lines.pop()

        for line in lines:
            self._lines.put(line)

        if not self._lines.empty():
            return self._lines.get()

    def send(self, msg, partial=False):
        assert self._im_producer, "Consumer is sending"

        if self._chan is None:
            return None

        try:
            ret = os.write(self._chan, msg)
            if not partial:
                os.write(self._chan, b"\n")
            return True
        except BrokenPipeError:
            return False

    def __del__(self):
        if self._chan is not None:
            os.close(self._chan)

        # the reader removes the pipe
        if self._path and not self._im_producer:
            os.remove(self._path)
        del self
