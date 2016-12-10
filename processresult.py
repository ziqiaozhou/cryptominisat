import os;
import re
import math
import sys
import matplotlib.pyplot as plt

def parsefile(filename):
    result=[]
    JIs=[]
    f=open(filename)
    minexp=10000000000
    for line in f:
        tmp=[]
        numexp=line.split('\t');
        for one in numexp:
            two=one.split('*')
            num=int(two[0])
            exp=int(two[1].replace('2^',''));
            if num>0:
                minexp=min(minexp,exp)
                tmp.append((num,exp))
        for k in range(0,len(tmp)):
            one=tmp[k]
            one[0]=one[0]*(math.pow(2,one[1]-minexp))
            one[1]=minexp
            tmp[k]=one
        diff=tmp[0][0]+tmp[1][0]-tmp[2][0]
        JI=((float(diff)/tmp[2][0]))
        result.append(tmp)
        JIs.append(JI)
    return (result,JI)


def getMid(count):
    nums=[]
    minexp=count[0][1]
    for numexp in count:
        minexp=min(minexp,numexp[1])
    for numexp in count:
        num=numexp[0]*(math.pow(2,(numexp[1]-minexp)));
        nums.append(num);
    lennum=len(nums)
    #return (sum(nums)/lennum,minexp)
    nums.sort()
    if(lennum%2==0):
        mid=(nums[lennum/2]+nums[lennum/2-1])/2
    else:
        mid=nums[(lennum-1)/2]
    return (mid,minexp);



def scan(Dir):
    Result={}
    JIs={}
    results={}
    resultnum=[]
    diffs=[]
    labels=[]
    for filename in os.listdir(Dir):
        if filename.startswith('count'):
            info=filename.split('_');
            jaccard=int(info[1].replace('j',''));
            result,JI=parsefile(Dir+'/'+filename)
            if jaccard in Result:
                Result[jaccard]=Result[jaccard]+result
                JIs[jaccard]=JI
            else:
                Result[jaccard]=result
                JIs[jaccard]=JIs[jaccard]+JI

'''    for jaccard in Result:
        result=getMid(Result[jaccard])
        results[jaccard]=result
		#resultnum.append(math.log(result[0],2)+(result[1]))
		#resultnum.append(1)
    #print Result
    #print results
    for jaccard in range(0,max(Result.keys())):
        if (jaccard in Result) and (jaccard+1 in Result):
            exp=results[jaccard][1]
            expsub=results[jaccard+1][1]
            minexp=min(exp,expsub)
            num=results[jaccard][0]
            diff1=exp-minexp
            num=num*(math.pow(2,diff1))
            numsub=results[jaccard+1][0]
            diff2=expsub-minexp
            numsub=numsub*(math.pow(2,diff2))
            labels.append(32-jaccard-1)
            if num>0:
                diff=float((numsub*2-num))/num
            else:
                diff=0
            if diff<=1:
                diffs.append(abs(diff))
            else:
                diffs.append(0)
            print jaccard,numsub,results[jaccard+1],minexp,expsub,'\t',num,results[jaccard],minexp,exp,'\t',numsub*2-num
            print results[jaccard],Result[jaccard]
            print results[jaccard+1],Result[jaccard+1]'''
    print Result,'\n',JI
    for jaccard in JI:
        diff=sum(JI[jaccard])/len(JI[jaccard])
        diffs.append(diff)
        labels.append(jaccard)
    print labels,diffs
    fig,ax=plt.subplots()
    ax.bar(labels,diffs)
    ax.set_xticks(labels)
    ax.set_xticklabels(tuple(labels))
    ax.set_xlabel('subset size')
    ax.set_ylabel('jaccard index')
    fig.savefig('result-diff.png')


if len(sys.argv)>1:
    scan(sys.argv[1])


