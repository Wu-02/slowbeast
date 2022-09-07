from slowbeast.domains.concrete_int_float import ConstantTrue
from slowbeast.ir.bblock import BBlock
from slowbeast.ir.instruction import Call, Branch


# FIXME: not efficient, but let's fix that once
# it is a problem
def split_after(block, after):
    B = BBlock(block.fun())
    blocks = [block]
    last = block.last()
    instructions = block.instructions().copy()
    for I in instructions:
        B.append(I)
        if after(I) and last != I:
            blocks.append(B)
            B = BBlock(block.fun())

    blocks.append(B)
    assert len(blocks) > 1
    # shrink the original block and make it jump
    # to the first new block (so that all the references
    # to the original block stay valid)
    block._instructions = []
    block.append(Branch(ConstantTrue, blocks[1], blocks[1]))
    for idx in range(1, len(blocks) - 1):
        blocks[idx].append(Branch(ConstantTrue, blocks[idx + 1], blocks[idx + 1]))
    return blocks


# FIXME: not efficient, but let's fix that once
# it is a problem


def split_around(block, P):
    B = BBlock(block.fun())
    blocks = [block]
    last = block.last()
    instructions = block.instructions().copy()
    for I in instructions:
        if P(I):
            # end previous block if non-empty
            if B.size() > 0:
                blocks.append(B)
                B = BBlock(block.fun())
            assert B.size() == 0
            B.append(I)
            blocks.append(B)
            if I != last:  # start new one
                B = BBlock(block.fun())
        else:
            B.append(I)

    blocks.append(B)
    assert len(blocks) > 1
    # shrink the original block and make it jump
    # to the first new block (so that all the references
    # to the original block stay valid)
    block._instructions = []
    block.append(Branch(ConstantTrue, blocks[1], blocks[1]))
    for idx in range(1, len(blocks) - 1):
        blocks[idx].append(Branch(ConstantTrue, blocks[idx + 1], blocks[idx + 1]))
    return blocks


def split_bblock_around_calls(block):
    if block.size() == 0:
        return [block]

    def iscall(c):
        return isinstance(c, Call)

    return split_around(block, iscall)


def split_fun_around_calls(F):
    F._bblocks = [
        b for block in F.bblocks().copy() for b in split_bblock_around_calls(block)
    ]


def split_program_around_calls(P):
    for F in P:
        split_fun_around_calls(F)
