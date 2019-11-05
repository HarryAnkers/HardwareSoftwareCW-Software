A = [5,4,3,2,1]
#B = [5,4,3,2,1]
for i in range(len(A)):
    for j in range(1,len(A)-i):
        print("(i,j,len(A) - i,A[j],A[k]) = "+str((i,j,len(A) - i,A[j-1],A[0:j])))
        if A[j-1] > A[j]:
            temp = A[j]
            A[j] = A[j-1]
            A[j-1] = temp
# print("-----------")
# for i in range(len(B)-1,0,-1):
#     for j in range(0,i):
#         print((i,j))
#         if B[j] > B[j+1]:
#             temp = B[j]
#             B[j] = B[j+1]
#             B[j+1] = temp

print("final - ")
print(A)
# print(B)