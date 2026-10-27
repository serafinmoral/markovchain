# -*- coding: utf-8 -*-
"""
Created on 31 Enero 2022

@author: Serafin
"""

from xmlrpc.client import boolean
import utils as u

import networkx as nx
import numpy as np
from SimpleClausulas import * 
from time import *
import math
import random


def tableunit(x):
    res = nodoTabla([abs(x)])
    if x>0:
        res.tabla[0] = False
    else:
        res.tabla[1] = False    
    return res



class mix:
    def __init__(self):
        self.lt = []
        self.unit = set()
        
        
    def anula(self):
        self.lt = []
        self.unit = set()


    def simplressubsumed(self,lp):
        if isinstance(lp,nodoTabla): 
            return False
        dif1 = lp.unit - self.unit
        dif2 = self.unit-lp.unit
        if len(dif1) == 1:
            vd = dif1.pop()
            if -vd in self.unit:     
                for q in lp.lt:
                    for v in dif2:
                        if v in q.getvars():
                            q = q.reduce(-v)
                    ok = False
                    for r in self.lt:
                        if r.implicadopor(q):
                            ok=True
                            break
                    if not ok:
                        return False
                self.unit.remove(-vd)
                return True
            else:
                laux = []
                for p in self.lt:
                    if vd in p.getvars():
                        p = p.reduce(vd)
                        laux.append(p)
                
                for q in lp.lt:
                    for v in dif2:
                        if v in q.getvars():
                            q = q.reduce(-v)
                    ok = False
                    for r in laux:
                        if r.implicadopor(q):
                            ok=True
                            break
                    if not ok:
                        return False
                self.lt = laux
                return True
        return False


        

    def implicadopor(self,lp):
        if isinstance(lp,nodoTabla): 
            for v in self.unit:
                if abs(v) in lp.getvars():
                   lp = lp.reduce(-v)
            for p in self.lt:
                if p.implicadopor(lp):
                    return True
            return False
        res = False
        if lp.unit <= self.unit:
            for q in lp.lt:
                for v in self.unit - lp.unit:
                    if abs(v) in q.getvars():
                        q = q.reduce(-v)
                ok = False
                for r in self.lt:
                    if r.implicadopor(q):
                        ok=True
                        break
                if not ok:
                    return False
            return True
        else:
            return False



        

    def getvars(self):
        res = set(self.unit)
        
        for x in self.lt:
            res.update(x.getvars())
        
        return res
    
    def toTable(self):
        res = nodoTabla([])
        res.tabla = False
        
        for p in self.lt:
            res = res.suma(p)

        for v in self.unit:
            p = tableunit(v)
            res = res.suma(p)
        
        return res
            

    def mtrivial(self):
        p = nodoTabla([])
        self.lt = [p]
        self.unit = set()

    def simplify(self,p):
        res = mix()

        if isinstance(p,nodoTabla):
            for q in self.lt:
                if set(p.getvars()) <= set(q.getvars()):
                    q = q.combina(p)
                    res.insert(q)
                else:
                    res.insert(q)

               

            return res
        
        
    def simplifyd(self,p,var): 
        res = mix()
        for q in self.lt:
                if set(p.getvars()) <= set(q.getvars()):
                    q = q.combina(p)
                    q = q.borra([var])
                    res.insert(q)
                else:
                    res.insert(q)

                

        return res  

    def borra(self,lista,Q=30):
        result = self
        sl1 = set(lista)
        sl2 = {abs(v) for v in self.unit}
        if sl1.intersection(sl2):
            result.mtrivial()
            return result
        result.unit = self.unit.copy()
        for p in self.lt:
            p = p.borra(lista,inplace=False)
            result.insert(p)
        
        return result
    
    
    
    def insert(self,p, group = False, Q=30):
     
        if self.trivial():
            return
        
        
        
        if isinstance(p,mix):
           
            for x in p.lt:
                self.insert(x)
            return
            
        
        
        if isinstance(p,nodoTabla):

            p = p.reduce([-v for v in self.unit])

            


            if not self.lt:
                if not p.contradict():
                    if p.trivial():
                        self.mtrivial()
                    else:
                        self.lt.append(p)
                return

            svar = set(p.getvars())
            q = min(self.lt , key = lambda x: len(set(x.getvars()).union(svar)) )

            if len(set(q.getvars()).union(svar)) <= Q and group:
                self.lt.remove(q)
                p = p.suma(q)
            elif len(set(q.getvars()).union(svar)) == len(svar):
                self.lt.remove(q)
                p = p.suma(q)

            if len(p.getvars()) ==1: 
                if p.trivial():
                    self.mtrivial()
                if not p.tabla[0] and p.tabla[1]:
                    if -p.getvars()[0] in self.unit:
                        self.mtrivial()
                        return
                    self.unit.add(p.getvars()[0])
                    self.regenerate(p.getvars()[0])
                elif p.tabla[0] and not p.tabla[1]:
                    if p.getvars()[0] in self.unit:
                        self.mtrivial()
                        return
                    self.unit.add(-p.getvars()[0])
                    self.regenerate(-p.getvars()[0])
                return


            if p.trivial():
                self.mtrivial()
                return
            
            if p.contradict():
                return

            self.lt.append(p)

            return 

        

            

    def regenerate(self,v):
        traba = self.lt.copy()
        self.lt = []
        ins = []

        for p in traba:
            if abs(v) not in p.getvars():
                self.lt.append(p)
            else:
                ins.append(p.reduce(-v))

        for p in ins:
            self.insert(p)

                
                
    def resolution(self,p,var):
            
            if isinstance(p,mix):
                r1 = mix()
                r2 = mix()
                p1 = p.reduce(var)
                p2 = p.reduce(-var)
                a1 = self.reduce(var)
                a2 = self.reduce(-var)
                sa1 = set(map(lambda x: -x, a1.unit))
                sa2 = set(map(lambda x: -x, a2.unit))
                if sa2.intersection(p1.unit):
                    r1.mtrivial()
                else:
                    r1.unit = a2.unit.union(p1.unit)
                if sa1.intersection(p2.unit):
                    r2.mtrivial()
                else:
                    r2.unit = a1.unit.union(p2.unit)
                  


                r1.insert(p1)
                r1.insert(a2)
                r2.insert(p2)
                r2.insert(a1)
            
                return (r1,r2)

            if isinstance(p,nodoTabla):
                r = mix()
                r.insert(p)
                return self.resolution(r,var)

            
               
    def combina(self,p):
        result = mix()
        if isinstance(p,nodoTabla):
            for q in self.lt:
                result.insert(q.combina(p,inplace= False))
            return result
        if isinstance(p,mix):
            if self.unit.intersection({-v for v in p.unit}):
                result.mtrivial()
                return result
            l1 = []
            l2 = []
            for q in self.lt: 
                for v in p.unit:
                    if abs(v) in q.getvars():
                        q= q.reduce(-v)
                l1.append(q)
            
            for r in p.lt:
                for v in self.unit:
                    if abs(v) in r.getvars():
                        r = r.reduce(-v)
                l2.append(r)
            for q in self.lt:
                  for r in p.lp:
                      h = q.combina(r)
                      result.insert(h)

            result.unit = self.unit.union(p.unit)
            return result
              


                  
                    

    def remove(self,p):
    
        if isinstance(p,nodoTabla):
            self.lt.remove(p)
        

        return 
        
            
    
    def reduce(self,v):
        res = mix()
        if isinstance(v,set):
            if self.unit.intersection(v):
                res.mtrivial()
                return res
            vn = set(map(lambda x: -x,v))
            res.unit = self.unit - vn
            for p in self.lt:
                h = p.reduce(v)
                res.insert(h)
                            

            return res
        
        if v in self.unit:
            res.mtrivial()
            return res
        if -v in self.unit:
            res.lt = self.lt.copy()
            res.unit = self.unit - {-v}
            return res
        var = abs(v)
        
        
        res.unit = self.unit.copy()
        
        for p in self.lt:
                if var in p.getvars():
                    h = p.reduce(v)
                    res.lt.append(h)
                else:
                    res.lt.append(p)
        return res

        


        
            



    def trivial(self):

        
        for x in self.lt:
            if x.trivial():
                return True
        return False

    def contradict(self):
        
        if self.unit:
            return False
        for p in self.lt:
            if not p.contradict():
                return False
        return True
        
            





class nodoTabla:

    
    def __init__(self, lista):
        
        self.listavar = lista
        n = len(lista)
        t = (2,)*n
        self.tabla = np.ones( dtype = boolean, shape = t)
        self.det = []
        self.mindet = []

    
    def copia(self):
        result = nodoTabla(self.listavar.copy())
        if isinstance(self.tabla,boolean) or isinstance(self.tabla,int):
            result.tabla = self.tabla
        else:
            result.tabla = self.tabla.copy()
        result.det = self.det.copy()
        result.mindet = self.mindet.copy()
        return result
    
    def getvars(self):
        return self.listavar
    
    def extrae2(self,vars):
        res = []
        if len(vars)>=2:
            for v in vars:
                res.extend(self.extrae2(vars-{v}))
                res.extend(self.extrae21(v,vars-{v}))
        return res

    def extrae21(self,v,vars):
        res = []
        for w in vars:
            p = self.borra(list(set(self.listavar) - {v,w}), inplace=False)
            if not p.trivial():
                res.append(p)
        return res



    def descomponev(self,v):
        res = []
        h = self.borra([v], inplace = False)

        

        t = self.minimiza(h, pro = {v})

        if len(t.listavar) ==len(self.listavar):
            res.append(self)
        else:
            res.append(t)
            res.append(h)


        return res



    def entropia(self,v):
            (x0,x1) = self.cuenta(v)
            if x0==0 or x1==0:
                return 0.0
            else:
                z0 = x0/(x0+x1)
                z1  = x1/(x0+x1)
                x = (-z0*math.log(z0) - z1*math.log(z1))
            return x
    
    def mincuenta(self,v):
            (x0,x1) = self.cuenta(v)
            return min(x0,x1)
            

    def minentropia(self):
            
            return min(self.listavar,key = lambda v: self.mincuenta(v))


    def neg(self,inplace=False):
        
        nuevatabla = np.logical_not(self.tabla)
        if inplace:
            self.tabla = nuevatabla
            res = self
        else:
            res = nodoTabla(self.listavar.copy())
            res.tabla = nuevatabla
            res.det = self.det.copy()
            res.mindet = self.mindet.copy()

        return res


    def equivalente(self,p):
       
        if not self.context == p.context:
            return False
        if self.suma(p.neg()).trivial() and p.suma(self.neg()).trivial():
            return True
        else:
            return False


    def implicadopor(self,p):

        if isinstance(p,mix) and p.unit:
            return False
        elif isinstance(p,mix):
            for h in p.lt:
                if not self.implicadopor(h):
                    return False
            return True
        

        if self.suma(p.neg()).trivial():
            return True
        else:
            return False

    def minimiza(self, con  , pro = set()):
        rest =  set(self.listavar)-pro
        if not rest:
            return self
        else:
            v = rest.pop()
            h = self.borra([v], inplace=False)
            if self.implicadopor(h.combina(con)):
                return h.minimiza(con,pro)
            else:
                pro.add(v)
                return self.minimiza(con,pro)





    def combina(self,op,inplace = False, des= False):

       
        
        if isinstance(self.tabla,boolean):
            if self.tabla:
                if inplace:
                    self = op.copia()
                    return self
                else:
                    return op.copia()
            else:
                if inplace:
                    return self
                else:
                    return self.copia()
            

            
        
        result = self if inplace else self.copia()
        

        result.det = result.det + [x for x in op.det if x not in result.det]
        result.mindet = []

        

        if isinstance(op.tabla,boolean):
            if op.tabla:
                return result
            else:
                result.tabla = nodoTabla([])
                result.anula()
                return result
        
        if not des:
            op = op.copia()
        extra = set(op.getvars()) - set(result.getvars())
        if extra:
                slice_ = [slice(None)] * len(result.getvars())
                slice_.extend([np.newaxis] * len(extra))

                result.tabla = result.tabla[tuple(slice_)]

                result.listavar.extend(extra)

        extra = set(result.getvars()) - set(op.getvars())
        if extra:
                slice_ = [slice(None)] * len(op.listavar)
                slice_.extend([np.newaxis] * len(extra))

                op.tabla = op.tabla[tuple(slice_)]

                op.listavar.extend(extra)
                # No need to modify cardinality as we don't need it.

            # rearranging the axes of phi1 to match phi
        for axis in range(result.tabla.ndim):
            exchange_index = op.listavar.index(result.listavar[axis])
            op.listavar[axis], op.listavar[exchange_index] = (
                op.listavar[exchange_index],
                op.listavar[axis],
            )
            op.tabla = op.tabla.swapaxes(axis, exchange_index)

        result.tabla = result.tabla & op.tabla    
        if not inplace:
            return result
        

    

    def combinab(self,op,inplace = False, des= False):
        from arboltabla import arbol

        if isinstance(op,arbol):
            return op.combina(self)
        
        if isinstance(self.tabla,boolean):
            if self.tabla:
                if inplace:
                    self = op.copia()
                    return self
                else:
                    return op.copia()
            else:
                if inplace:
                    return self
                else:
                    return self.copia()
                
        
            
        if isinstance(self.tabla,float)or isinstance(self.tabla,int) :
                x = self.tabla
                if inplace:
                    
                    self = op
                    self.tabla = self.tabla*x
                    return self
                else:
                    h = op.copia()
                    h.tabla = h.tabla*self.tabla
                    return h
        
            

        result = self if inplace else self.copia()

        if isinstance(op.tabla,boolean):
            if op.tabla:
                return result
            else:
                result.tabla = nodoTabla([])
                result.anula()
                return result
        
        if not des:
            op = op.copia()
        extra = set(op.getvars()) - set(result.getvars())
        if extra:
                slice_ = [slice(None)] * len(result.getvars())
                slice_.extend([np.newaxis] * len(extra))

                result.tabla = result.tabla[tuple(slice_)]

                result.listavar.extend(extra)

        extra = set(result.getvars()) - set(op.getvars())
        if extra:
                slice_ = [slice(None)] * len(op.listavar)
                slice_.extend([np.newaxis] * len(extra))

                op.tabla = op.tabla[tuple(slice_)]

                op.listavar.extend(extra)
                # No need to modify cardinality as we don't need it.

            # rearranging the axes of phi1 to match phi
        for axis in range(result.tabla.ndim):
            exchange_index = op.listavar.index(result.listavar[axis])
            op.listavar[axis], op.listavar[exchange_index] = (
                op.listavar[exchange_index],
                op.listavar[axis],
            )
            op.tabla = op.tabla.swapaxes(axis, exchange_index)

        result.tabla = result.tabla * op.tabla    
        if not inplace:
            return result

    

    def divideb(self,op,inplace = False, des= False):
        from arboltabla import arbol

        if isinstance(op,arbol):
            return op.combina(self)
        
        if isinstance(self.tabla,boolean):
            if self.tabla:
                if inplace:
                    self = op.copia()
                    return self
                else:
                    return op.copia()
            else:
                if inplace:
                    return self
                else:
                    return self.copia()
            

            

        result = self if inplace else self.copia()

        if isinstance(op.tabla,boolean):
            if op.tabla:
                return result
            else:
                result.tabla = nodoTabla([])
                result.anula()
                return result
        
        if not des:
            op = op.copia()
        extra = set(op.getvars()) - set(result.getvars())
        if extra:
                slice_ = [slice(None)] * len(result.getvars())
                slice_.extend([np.newaxis] * len(extra))

                result.tabla = result.tabla[tuple(slice_)]

                result.listavar.extend(extra)

        extra = set(result.getvars()) - set(op.getvars())
        if extra:
                slice_ = [slice(None)] * len(op.listavar)
                slice_.extend([np.newaxis] * len(extra))

                op.tabla = op.tabla[tuple(slice_)]

                op.listavar.extend(extra)
                # No need to modify cardinality as we don't need it.

            # rearranging the axes of phi1 to match phi
        for axis in range(result.tabla.ndim):
            exchange_index = op.listavar.index(result.listavar[axis])
            op.listavar[axis], op.listavar[exchange_index] = (
                op.listavar[exchange_index],
                op.listavar[axis],
            )
            op.tabla = op.tabla.swapaxes(axis, exchange_index)
        
        result.tabla = result.tabla/op.tabla   

        result.tabla[np.isnan(result.tabla)] = 0


            

          
        if not inplace:
            return result


    def checkdetermi(self,v):
        if v not in self.listavar:
            return False
        t0 = self.reduce([v])
        t1 = self.reduce([-v])

       

        t = t0.combina(t1, inplace=False)

        if t.contradict():
            self.mindet = []
            self.det.append(v)
            return True
        else:
            return False

    def contenida(self,listanodos):
        return u.contenida(self,listanodos) 

    def minimizadep(self,v, seg = None):
        if v in self.mindet:
            return self
        if not seg:
            seg = set()
        vars = set(self.listavar) - seg
        vars.remove(v)

        if not vars:
            self.mindet.append(v)
            return self
        
        
        nv = vars.pop()

        np = self.borra([nv])

        

        if not np.trivial() and np.checkdetermi(v):
            
            return np.minimizadep(v, seg.copy())
        else:
            seg.add(nv)
            return self.minimizadep(v,seg)


    def extraesimple(self):
        
        vars = set(self.listavar)
        if not vars:
            return nodoTabla([])
        v = vars.pop()

        pv = self.borra(list(vars))
        if not pv.trivial():
            return pv
        else:
            pr = self.borra([v])

            if not pr.trivial():
                sr = pr.extraesimple()
                if not sr.trivial():
                    return sr
                else:
                    h2 = self.extrasimple2(v,vars)
                    return h2
            else:
                return nodoTabla([])

    def mejora(self,q):
            vars = list(set(q.listavar) - set(self.listavar))
            res = self.combina(q.borra(vars))
            return res

    def extrasimple2(self,v1,vars):
        if not vars:
            return nodoTabla([])
        v2 = vars.pop()

        pv12 = self.borra(list(vars))

        if pv12.checkdetermi(v2) or pv12.checkdetermi(v1):
            return pv12
        else:
            pr = self.borra([v2])

            return pr.extrasimple2(v1,vars)



    


    def suma(self,op,inplace = False, des= False):
        result = self if inplace else self.copia()
        result.det = self.det.copy()
        result.mindet = self.mindet.copy()
        if isinstance(op.tabla,boolean):
            if op:
                return result
            else:
                result.tabla = result.tabla | op.tabla
                return result
            
        if isinstance(self.tabla,boolean):
            if self.tabla:
                return result
            else:
                    result = op.copia()
                    return result
                

                
            

        if not des:
            op = op.copia()
        extra = set(op.listavar) - set(result.listavar)
        if extra:
                slice_ = [slice(None)] * len(result.listavar)
                slice_.extend([np.newaxis] * len(extra))

                result.tabla = result.tabla[tuple(slice_)]

                result.listavar.extend(extra)

        extra = set(result.listavar) - set(op.listavar)
        if extra:
                slice_ = [slice(None)] * len(op.listavar)
                slice_.extend([np.newaxis] * len(extra))

                op.tabla = op.tabla[tuple(slice_)]

                op.listavar.extend(extra)
                # No need to modify cardinality as we don't need it.

            # rearranging the axes of phi1 to match phi
        for axis in range(result.tabla.ndim):
            exchange_index = op.listavar.index(result.listavar[axis])
            op.listavar[axis], op.listavar[exchange_index] = (
                op.listavar[exchange_index],
                op.listavar[axis],
            )
            op.tabla = op.tabla.swapaxes(axis, exchange_index)

        result.tabla = result.tabla | op.tabla    
        if not inplace:
            return result



    def sumab(self,op,inplace = False, des= False):
        result = self if inplace else self.copia()
        if isinstance(op.tabla,boolean):
            if op:
                return result
            else:
                result.tabla = result.tabla | op.tabla
                return result
            
        if isinstance(self.tabla,boolean):
            if self.tabla:
                return result
            else:
                    result = op.copia()
                    return result
                

                
            

        if not des:
            op = op.copia()
        extra = set(op.listavar) - set(result.listavar)
        if extra:
                slice_ = [slice(None)] * len(result.listavar)
                slice_.extend([np.newaxis] * len(extra))

                result.tabla = result.tabla[tuple(slice_)]

                result.listavar.extend(extra)

        extra = set(result.listavar) - set(op.listavar)
        if extra:
                slice_ = [slice(None)] * len(op.listavar)
                slice_.extend([np.newaxis] * len(extra))

                op.tabla = op.tabla[tuple(slice_)]

                op.listavar.extend(extra)
                # No need to modify cardinality as we don't need it.

            # rearranging the axes of phi1 to match phi
        for axis in range(result.tabla.ndim):
            exchange_index = op.listavar.index(result.listavar[axis])
            op.listavar[axis], op.listavar[exchange_index] = (
                op.listavar[exchange_index],
                op.listavar[axis],
            )
            op.tabla = op.tabla.swapaxes(axis, exchange_index)

        result.tabla = result.tabla + op.tabla    
        if not inplace:
            return result


    def reduce(self, val, inplace=False):

        if isinstance(val,int):
            return self.reduce([val])
        
        values = filter(lambda x: abs(x) in  self.listavar, val)
        phi = self if inplace else nodoTabla([])


        phi.mindet = []
        phi.det = []

        
        values = [
                (abs(var), 0 if var<0 else 1) for var in values
            ]
        
        if not values:
            if inplace:
                return self
            else:
                return self.copia()
            
        var_index_to_del = []
        slice_ = [slice(None)] * len(self.listavar)
        for var, state in values:
            var_index = self.listavar.index(var)
            slice_[var_index] = state
            var_index_to_del.append(var_index)

        var_index_to_keep = sorted(
            set(range(len(self.listavar))) - set(var_index_to_del)
        )
        # set difference is not guaranteed to maintain ordering
        phi.listavar = [self.listavar[index] for index in var_index_to_keep]
        

        phi.tabla= self.tabla[tuple(slice_)]

        
        return phi

    def getvalue(self, val):
        
        values = filter(lambda x: abs(x) in  self.listavar, val)
        vars = map(abs,val)

        rest = set(self.listavar) - set(vars)
        if rest:
            return -1

        values = [
                (abs(var), 0 if var<0 else 1) for var in values
            ]

        var_index_to_del = []
        slice_ = [slice(None)] * len(self.listavar)
        for var, state in values:
            var_index = self.listavar.index(var)
            slice_[var_index] = state
            var_index_to_del.append(var_index)

        
        

        return self.tabla[tuple(slice_)]

        
    def setvalue(self, val,x):
        
        values = filter(lambda x: abs(x) in  self.listavar, val)
        vars = map(abs,val)

        rest = set(self.listavar) - set(vars)
        if rest:
            return -1

        values = [
                (abs(var), 0 if var<0 else 1) for var in values
            ]

        var_index_to_del = []
        slice_ = [slice(None)] * len(self.listavar)
        for var, state in values:
            var_index = self.listavar.index(var)
            slice_[var_index] = state
            var_index_to_del.append(var_index)

        
        

        self.tabla[tuple(slice_)] = x

        
    
    def introducelista(self,lista):
        for cl in lista:
            self.introduceclau(cl)
    
    def introduceclau(self, values):
        for var in values:
            if abs(var) not in self.listavar:
                raise ValueError(f"La variable: {abs(var)} no está en el potencial")


        values = [
                (abs(var), 1 if var<0 else 0) for var in values
            ]

        slice_ = [slice(None)] * len(self.listavar)
        for var, state in values:
            var_index = self.listavar.index(var)
            slice_[var_index] = state

        
        # set difference is not guaranteed to maintain ordering
        

        self.tabla[tuple(slice_)] = False

        

    def introduceclaun(self, values):
        for var in values:
            if abs(var) not in self.listavar:
                raise ValueError(f"La variable: {abs(var)} no está en el potencial")


        values = [
                (abs(var), 0 if var<0 else 1) for var in values
            ]

        slice_ = [slice(None)] * len(self.listavar)
        for var, state in values:
            var_index = self.listavar.index(var)
            slice_[var_index] = state

        
        # set difference is not guaranteed to maintain ordering
        

        self.tabla[tuple(slice_)] = False

    def checkxor(self):
        index = np.argwhere(self.tabla)
        even = all( sum(x) % 2==0 for x in index )
        odd = all( sum(x) % 2==1 for x in index )

        if even:
            return (set(self.getvars()),False)
        
        if odd:
            return (set(self.getvars()),True)
        
        return False
            
        

    def borra(self,variables, inplace=False):

        phi = self if inplace else self.copia()   
        for var in variables:
            if var not in phi.listavar:
                raise ValueError(f"{var} no está en la lista.")
        phi.det = []
        phi.mindet = []
        

        var_indexes = [phi.listavar.index(var) for var in variables]

        index_to_keep = sorted(set(range(len(self.listavar))) - set(var_indexes))
        phi.listavar = [phi.listavar[index] for index in index_to_keep]

        phi.tabla = np.amax(phi.tabla, axis=tuple(var_indexes))

        if not inplace:
            return phi
        
           



    def contradict(self):
        return not np.amax(self.tabla)

    def cuenta(self,v):
        t0 = self.reduce([v],inplace=False)
        t1 = self.reduce([-v],inplace=False)
        x0 = np.sum(t0.tabla)
        x1 = np.sum(t1.tabla)
        return (x0,x1)

    def anula(self):
        
        
        
        self.listavar = []
        self.tabla = np.zeros(dtype = boolean, shape = ())

    def trivial(self):
        return  np.amin(self.tabla)

    def calculaunit(self):
        result = set()
        n = len(self.listavar)
        if n==0:
            if not self.tabla:
                result.add(0)
            return result
        elif n==1:
            if not self.tabla[0]:
                if not self.tabla[1]:
                    result.add(0)
                    return result
                else:
                    result.add(self.listavar[0])
            elif not self.tabla[1]:
                result.add(-self.listavar[0])
            return result
        
        total = set(range(n))
        
            
        borra = tuple(total-{n-1})
        marg = np.amax(self.tabla,axis = borra)
        
        if not marg[0]:
            if not marg[1]:
                result.add(0)
                return result
            else:
                result.add(self.listavar[n-1])
        elif  not marg[1]:    
                result.add(-self.listavar[n-1])

        if 0 in result:
            return result
        h = self.borra([self.listavar[n-1]],inplace=False)
        result.update(h.calculaunit())

        return result

    def univar(self):
        if not len(self.getvars()) ==1:
            return None
        if not self.tabla[0] and self.tabla[1]:
            return self.gervars()[0]
        if self.tabla[0] and not self.tabla[1]:
            return -self.gervars()[0]
        return None
        
          
    
    def resolution(self,p,var):
        
        if isinstance(p,nodoTabla):
            r1 = mix()
            r2 = mix()
            p1 = p.reduce(var)
            p2 = p.reduce(-var)
            a1 = self.reduce(var)
            a2 = self.reduce(-var)
            r1.insert(p1)
            r1.insert(a2)
            r2.insert(p2)
            r2.insert(a1) 
            return (r1,r2)
            
        if isinstance(p,mix):
            return p.resolution(self,var)
        
               
                        


            

    







