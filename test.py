from tableau import PriorityQueue

q = PriorityQueue()
for i in range(10):
    q.introduceConstant()
    print([i.name for i in q.getAllConstants()])
assert q.introduceConstant() is None
