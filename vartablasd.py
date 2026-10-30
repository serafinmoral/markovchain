# -*- coding: utf-8 -*-
"""
Created on 31 Enero 2022

@author: Serafin
Adaptado para compatibilidad con nodoTabla en PyTorch
"""
from statistics import variance
from time import *
from random import shuffle, choices, choice
from tablaClausulas import *
from itertools import combinations, product
from utils import *
import utils as u
import torch
import math

def borralista(lista, delv, Q):
    while delv:
        w = siguientelista(lista, delv)
        delv.remove(w)
        lw = []
        for p in lista:
            if w in p.getvars():
                lw.append(p)
        for p in lw:
            lista.remove(p)
        deter = False
        for p in lw:
            if w in p.det:
                borradet(w, lw, p, lista, Q)
                deter = True
                break
        if not deter:
            q = nodoTabla([])
            tvars = set()
            while lw:
                p = min(lw, key=lambda x: len(tvars.union(set(x.getvars()))))
                lw.remove(p)
                tvars.update(set(p.getvars()))
                if len(tvars) <= Q or not(q.getvars()):
                    q = q.combina(p)
                elif w in q.getvars():
                    q = q.borra([w])
                    lista.append(q)
                    q = p
                    tvars = set(p.getvars())
            if w in q.getvars():
                q = q.borra([w])
                lista.append(q)

def siguientelista(lista, delv):
    l = dict()
    for v in delv:
        l[v] = []
    for p in lista:
        for v in p.getvars():
            if v in delv:
                l[v].append(p)
    for v in delv:
        if len(l[v]) <= 1:
            return v
    return min(delv, key=lambda x: computesize(l[x]))

def borradet(w, lw, p, lista, Q):
    lw.remove(p)
    if not lw:
        lista.append(p.borra([w], inplace=False))
    else:
        for q in lw:
            if len(set(p.getvars()).union(set(q.getvars()))) <= Q:
                h = p.combina(q, inplace=False).borra([w], inplace=False)
                lista.append(h)
            else:
                lista.append(q.borra([w], inplace=False))

def recompute(w, list, config, remain):
    w.clear()
    k = set(remain) - {abs(v) for v in config}   
    for v in k:
        pos = 1.0
        neg = 1.0
        for p in list:
            if v in p.getvars() and len(set(p.getvars()) - {abs(i) for i in config}) <= 4:
                (x, y) = p.cuenta(v)
                pos *= x
                neg *= y
                s = pos + neg
                if s > 0:
                    pos = pos / s
                    neg = neg / s
        if pos == 0 and neg == 0:
            pos = 0.5 
            neg = 0.5
        w[v] = (pos, neg)

def calculate_entropy(x, y):
    total = x + y
    if total == 0:
        return float('inf') # Ignore keys with no data
    
    p_x = x / total
    p_y = y / total
    
    entropy = 0
    if p_x > 0: entropy -= p_x * math.log(p_x)
    if p_y > 0: entropy -= p_y * math.log(p_y)
    
    return entropy

# Find the key that minimizes the entropy
def getInitial(remain, list):
    config = set()
    w = dict()
    
    while len(config) < len(remain):
        recompute(w, list, config, remain)
        v = min(w, key=lambda k: calculate_entropy(w[k][0], w[k][1]))

        value = choices([v, -v], weights=w[v])
        config.add(value[0])
     
    return config


def getl(l, x):
    li = []
    h = set(x)
    for p in l:
        if set(p.getvars()).intersection(h):
            li.append(p)
    return li

def update(value, dvar, dvard, total):
    for x in total:
        value[x] = 0.0
        lista1 = dvar.get(x, [])
        lista2 = dvard.get(x, [])
        if lista2:
            pivote = min(lista2, key=lambda y: len(y))
            for p in lista1:
                value[x] += 2**(len(pivote.union(p)) - 1) - 2**(len(p))
            
            for p in lista2:
                if not p == pivote:
                    value[x] += 2**(len((pivote.union((p)))) - 1) - 2**(len(p))
        else:
            t = set()
            for p in lista1:
                value[x] -= - 2**(len(p))
                t.update(p)
            value[x] += 2**(len(t) - 1)

def updateclus(x, dvar, dvard):
    res = set()
    lista1 = dvar.get(x, [])
    lista2 = dvard.get(x, [])
    nue = []

    if lista2:
        pivote = min(lista2, key=lambda y: len(y))
        res.update(pivote)
        for p in lista1:
            nue.append(p.union(pivote) - {x})
            res.update(p)

        for p in lista2:
            if not p == pivote:
                nue.append(p.union(pivote) - {x})
                res.update(p)
    else:
        for p in lista1:
            res.update(p)
        nue.append(res)

    for v in res:
        dvar[v] = list(filter(lambda z: x not in z, dvar.get(v, [])))
        dvard[v] = list(filter(lambda z: x not in z, dvard.get(v, [])))

    res.discard(x)
   
    for p in nue:
        for v in p:
            if v in dvar:
                dvar[v].append(p)
            else:
                dvar[v] = [p]

    return res

def groupp(l, Q=30):
    if not l:
        return
    ln = l.copy()
    t = min(ln, key=lambda x: len(x.getvars()))   
    l.remove(t) 
    ln.remove(t)
    while ln:
        h = min(ln, key=lambda x: len(set(x.getvars()).union(set(t.getvars()))))
        if len(set(h.getvars()).union(set(t.getvars()))) <= Q:
            t = t.combina(h)
            ln.remove(h)
            l.remove(h)
        else:
            l.append(t)
            t = min(ln, key=lambda x: len(t.getvars()))   
            ln.remove(t)
            l.remove(t)
    l.append(t)

def ordena(l, Q):
    lc = l.copy()
    l.clear()

    while lc:
        q = min(lc, key=lambda x: len(x.getvars()))
        lc.remove(q)
        l.append(q)
        lista = set(q.getvars())
        while lc:
            q = min(lc, key=lambda x: len(lista.union(set(x.getvars()))))
            if len(lista.union(set(q.getvars()))) <= Q:
                lc.remove(q)
                l.append(q)
                lista.update(set(q.getvars()))
            else:
                break
            
def computesize(list):
    vs = set()
    for p in list:
        vs.update(set(p.getvars()))
    return len(vs)

def computevars(list):
    vs = set()
    for p in list:
        vs.update(set(p.getvars()))
    return vs


def mejora(p, lista, Q):
    traba = lista.copy()
    old = p.tabla.sum().item() if isinstance(p.tabla, torch.Tensor) else int(p.tabla)
    if p in traba:
        traba.remove(p)
    vas = computevars(lista)
    vap = set(p.getvars())
    vdel = vas - vap
    borralista(traba, vdel, Q)
    
    for q in traba:
        p.combina(q, inplace=True)

    new = p.tabla.sum().item() if isinstance(p.tabla, torch.Tensor) else int(p.tabla)
    if new < old:
        print("mejora", new, old, 2**(len(p.getvars())), new / 2**(len(p.getvars())), old / 2**(len(p.getvars())))
        return True
    else:
        return False


class varpot:

    def __init__(self): 
        self.tablas = dict()
        self.unit = set()
        self.contradict = False
        self.tablam = dict()
        self.orden = []
        self.compiled = dict()
        self.posvar = dict()
        self.prob = dict()
        self.svars = set()
        self.det = dict()
        self.wait = dict()
        self.hypertree = dict()
        self.parent = dict()
        self.hyperpot = dict()
        self.w = 1
        self.Q = 26
        self.A = -1
        self.tocont = False
        self.second = False
            
    def reset(self):
        for v in self.orden:
            self.insertar(self.compiled[v])
            if v in self.wait:
                for p in self.wait[v]:
                    self.insertar(p)
        self.wait = dict()
        self.orden = []
        self.posvar = dict()
        self.compiled = dict()
        self.det = dict()
        self.A = len(self.svars)

    def preset(self, L=25, total=True):
        if self.A == -1:
            return
        listi = []
        listd = []
        if total:
            K = 0
        else:
            K = self.A
        for i in range(K, len(self.orden)):
            v = self.orden[i]
            listi.append(self.compiled[v])
            if v in self.wait:
                for p in self.wait[v]:
                    listi.append(p)
                del self.wait[v]
            if self.det[v] and len(self.compiled[v].getvars()) <= L and v in self.compiled[v].getvars():
                listd.append((v, self.compiled[v]))
            del self.compiled[v]
            del self.posvar[v]
            del self.det[v]

        for p in listi:
            for (v, q) in listd:
                if not(p == q) and set(q.getvars()) <= set(p.getvars()):
                    p = p.combina(q).borra([v])
                    print("reduzco ", len(p.getvars()))
            self.insertar(p)

        del self.orden[K:]
        self.A = -1
        
    def anula(self):
        self.tablas = dict()
        self.tablasch = dict()
        self.contradict = True
        self.tablasize = dict()
        self.unit = set()
        self.compiled = dict()
        self.wait = dict()
        self.A = -1

    def getvars(self):
        res = set(map(abs, self.unit))
        for v in self.tabla:
            if self.tabla[v]:
                res.add(v)
        return res

    def computefromBayes(self, tables, evid):
        self.w = 1
        tar = []
        for p in tables:
            q = p.reduce(evid)
            tar.append(q)
        for x in evid:
            p = tableunit(x)
            self.insertar(p)
            self.svars.add(abs(x))
        for p in tar:
            self.insertbay(p)
            self.svars.update(p.getvars())
           
            q = nodoTabla(p.listavar, device=p.device)
            q.tabla = p.tabla > 0
            if not q.trivial():
                self.insertar(q)

    def computefromSimple(self, infor):
        self.w = 1
        self.svars = infor.listavar.copy()
        self.A = -1
        self.unit = infor.unit.copy()

        (sets, clusters) = u.createclusters(infor.listaclaus)
        for i in range(len(sets)):
            p = nodoTabla(list(sets[i]))
            p.introducelista(clusters[i])
            self.insertar(p)

    def eliminar(self, p):
        if len(p.getvars()) == 1:
            if not bool(p.tabla[0]) and bool(p.tabla[1]):
                self.unit.remove(p.getvars()[0])
            elif bool(p.tabla[0]) and not bool(p.tabla[1]):
                self.unit.remove(-p.getvars()[0])

        for v in p.getvars():
            self.tablas[v].remove(p)
        return

    def insertvar(self, v):
        if v in self.unit:
            return
        if -v in self.unit:
            self.anula()
            return
        self.unit.add(v)
        self.regenerate(v)

    def insertarsecond(self, p, R=15):
        if self.contradict:
            return []
        p = p.reduce(self.unit)

        if p.trivial():
            print("trivial ")
            return []

        if p.contradict():
            self.anula()
            return

        tvars = p.getvars()
        po = min(self.posvar[v] for v in tvars)
        w = self.orden[po]

        print(len(self.orden) - po, len(self.compiled[w]))

        if isinstance(p, mix) and len(p.getvars()) <= R:
            self.insertarsecond(p.toTable())
            return

        if isinstance(p, nodoTabla) and len(p.getvars()) == 1:
            v = p.univar()
            self.insertvar(v)
            return

        if isinstance(p, nodoTabla) and self.det[w]:
            print("inserto tabla determinista ")
            q = self.compiled[w][0]
            old = len(q.getvars())
            vd = set(p.getvars()) - set(q.getvars())
            h = p.borra(list(vd), inplace=False)
            self.compiled[w][0] = self.compiled[w][0].combina(h)
            self.compiled[w][0] = self.compiled[w][0].minimizadep(w)
            new = len(self.compiled[w][0].getvars())
            if new < old:
                self.simplifydet(self.compiled[w][0], w)
                print("reduzco determinismo ", old - new)
            
            if len(set(p.getvars()).union(q.getvars())) <= self.Q:
                h = p.combina(q)
                h = h.borra([w], inplace=False)
                self.insertarsecond(h)
                return
            else:
                (h1, h2) = p.resolution(q, w)
                self.insertarsecond(h1)
                self.insertarsecond(h2)
                return

        if isinstance(p, nodoTabla) and not self.det[w]:
            print("inserto tabla no determinista ")
            included = False
            for i in range(len(self.compiled[w])):
                q = self.compiled[w][i]
                if len(set(p.getvars()).union(set(q.getvars()))) <= self.Q:
                    if not included:
                        r = q.combina(p)
                        included = True
                        self.compiled[w][i] = r # Corregido self.compiled[i] -> self.compiled[w][i]
                    else:
                        q = q.combina(p, inplace=False)
                    h = r.borra([w], inplace=False)
                    self.insertarsecond(h)
                else:
                    (h1, h2) = p.resolution(q, w)
                    self.insertarsecond(h1)
                    self.insertarsecond(h2)
                    
            if not included:
                self.compiled[w].append(p)
            else:
                d = r.checkdetermi(w)
                if d:
                    print("nuevo determinismo ", len(r.getvars()))
                    h = r.minimizadep(w)
                    self.simplifydet(h, w)
                    self.compiled[w] = [h]
                    self.det[w] = True
            return

        if isinstance(p, mix) and self.det[w]:
            print("inserto mix determinista")
            q = self.compiled[w][0]
            (h1, h2) = p.resolution(q, w)
            self.insertarsecond(h1)
            self.insertarsecond(h2)
            return

        if isinstance(p, mix) and not self.det[w]:
            print("inserto mix no determinista")
            for q in self.compiled[w]:
                print(len(self.compiled[w]))
                (h1, h2) = q.resolution(p, w)
                print("inserto primero ")
                self.insertarsecond(h1)
                print("inserto segundo")
                self.insertarsecond(h2)

            self.compiled[w].append(p)
            return

    def insertar(self, p):
        p = p.reduce(self.unit)
        if self.contradict:
            return []
        
        svar = set(p.getvars())
        if p.trivial():
            return []
        
        p = self.checkequal(p)    

        if p.contradict():
            self.anula()
            return

        if len(p.getvars()) == 1:
            if not bool(p.tabla[0]) and bool(p.tabla[1]):
                if -p.getvars()[0] in self.unit:
                    self.anula()
                    return
                self.unit.add(p.getvars()[0])
                self.regenerate(p.getvars()[0])
            elif bool(p.tabla[0]) and not bool(p.tabla[1]):
                if p.getvars()[0] in self.unit:
                    self.anula()
                    return
                self.unit.add(-p.getvars()[0])
                self.regenerate(-p.getvars()[0])

        for v in svar:
            if v in self.tablas:
                self.tablas[v].append(p)
            else:
                self.tablas[v] = [p]
        return

    def simplifydet(self, q, var):
        if not self.second:
            return
        if var in self.tablas.get(var, []):
            for p in self.tablas[var]:
                if set(q.getvars()) <= set(p.getvars()):
                    self.eliminar(p)
                    self.insertar(p.combina(q).borra([var], inplace=False))
            n = self.posvar[var]
            for i in range(n - 1, self.A - 1, -1):
                va = self.orden[i]
                if not self.second:
                    p = self.compiled[va]
                    if isinstance(q, nodoTabla) and set(q.getvars()) <= set(p.getvars()):
                        self.compiled[va] = p.combina(q).borra([var], inplace=False)
                else:
                    aux = []
                    for qp in self.compiled[va]:
                        if isinstance(qp, nodoTabla) and set(q.getvars()) <= set(qp.getvars()):
                            qp = qp.combina(q).borra([var], inplace=False)
                        aux.append(qp)
                    self.compiled[va] = aux

                if va in self.wait:
                    aux = []
                    for qp in self.wait[va]:
                        if isinstance(qp, nodoTabla) and set(q.getvars()) <= set(qp.getvars()):
                            qp = qp.combina(q).borra([var], inplace=False)
                        aux.append(qp)
                    self.wait[va] = aux
        
            self.det[var] = True
            if self.second:
                self.compiled[var] = [q]
            else:
                self.compiled[var] = q

    def regenerate(self, v, second=False):
        var = abs(v)
        if var in self.tablas:
            lista = self.tablas[var].copy()
            for p in lista:
                self.eliminar(p)
            for p in lista:
                q = p.reduce([v])
                self.insertar(q)
        if var in self.posvar:
            K = self.posvar[var] - 1
        else:
            K = len(self.orden) - 1
        if self.A == -1:
            L = -1
        else:
            L = self.A -1
        for i in range(K, L, -1):
            va = self.orden[i]
            if self.second:
                for j in range(len(self.compiled[va])):
                    if var in self.compiled[va][j].getvars():
                        self.compiled[va][j] = self.compiled[va][j].reduce([v])
            else:
                if va in self.compiled and var in self.compiled[va].getvars():
                    self.compiled[va] = self.compiled[va].reduce([v])
                    
            if va in self.wait:
                for j in range(len(self.wait[va])):
                    if var in self.wait[va][j].getvars():
                        self.wait[va][j] = self.wait[va][j].reduce([v])

        self.det[var] = True
        if self.second:
            self.compiled[var] = [tableunit(v)]
        else:
            self.compiled[var] = tableunit(v)

    def computehyper(self):
        for v in self.orden:
            self.hypertree[v] = set(self.compiled[v].getvars())
            self.hyperpot[v] = [self.compiled[v]]
            if v in self.wait:
                for p in self.wait[v]:
                    self.hypertree[v].update(set(p.getvars()))
                self.hyperpot[v].extend(self.wait[v])
                    
        for v in self.orden:
            wv = set(self.hypertree[v]) - {v}
            if wv:
                self.parent[v] = min([self.posvar[w] for w in wv])
                self.hypertree[self.orden[self.parent[v]]].update(self.hypertree[v] - {v})
            else:
                self.parent[v] = -1

    def compile(self, verb=True, H=10):
        self.Q = H
        self.compiletotal()
        print(len(self.orden) - self.A)
        self.computehyper()
        self.compileup()
        self.mejoraup()
        count = 0
        for i in range(200):
            old = self.A     
            print(">>>>>>>>>>>>>>>Q= ", self.Q)
            sleep(1)
              
            self.preset()
            self.compiletotal()
            new = self.A

            print(len(self.orden) - self.A)
            if self.contradict:
                break
            self.computehyper()
            self.compileup()
            ok = self.mejoraup()

            if new <= old:
                count+= 1
            else:
                count = 0
            if count == 20 and self.Q == 25:
                break
            if count == 3 and self.Q<25:
                count = 0
                self.Q+= 1
            
            

        

        if not self.A == -1:
            self.preset()
            remain = self.svars - set(self.orden)  
            remain = remain - set(map(abs, self.unit))
            v = self.choose(remain)
            print("elijo ", v)
            sleep(5)
            pos = self.reduce(v)
            pos.compile(H=25)
            if pos.contradict:
                print("contradiccion ")
                sleep(2)
                self = self.reduce(-v)
                self.compile(H=25)
            else:
              print("solucion encontrada con ", v)
              pos = self.reduce(-v)
              pos.compile(H=25)  
              if pos.contradict:
                self = self.reduce(v)
                self.compile(H=25)
              else:
                 print("solucion encontrada con ", -v)


    def compilesecond(self):
        for v in self.orden[:self.A - 1:-1]:
            print(v, self.posvar[v])
            if v in self.wait:
                print("wait", len(self.wait[v]))
                for q in self.wait[v]:
                    print("inserto ")
                    self.insertarsecond(q)
                del self.wait[v]      

    def mejoraup(self, partial=True):
        if partial:
            K = self.A
        else:
            K = 0

        ok = False
        for v in self.orden[K:]:
            th = mejora(self.compiled[v], self.hyperpot[v], self.Q)
            ok = th|ok
            if v in self.wait:
                for p in self.wait[v]:
                    th = mejora(p, self.hyperpot[v], self.Q) 
        return ok

    def compileup(self, partial=True):
        print("entro en compile up")
        for i in range(len(self.orden) - 1, self.A - 1, -1):
            v = self.orden[i]
            if self.parent[v] > -1:
                varpa = self.orden[self.parent[v]]
                lista = self.hyperpot[varpa].copy()
                lvp = self.hypertree[varpa]
                lvt = self.hypertree[v]
                delv = lvp - lvt
                borralista(lista, delv, self.Q)
                self.hyperpot[v] = self.hyperpot[v] + lista
        print("salgo compile up")

    def compiledet(self, verb=True):
        remain = self.svars - set(self.orden)        
        remain = remain - set(map(abs, self.unit))
        K = len(remain)
        while remain:
            var = self.siguientep(remain)
            remain.remove(var)
            d = self.borrasidet(var, K)
            if not d:
                ok = self.compilevar(var)       

    def compiletotal(self, wait=True, test=True, verb=True):
        remain = self.svars - set(self.orden)  
        remain = remain - set(map(abs, self.unit))     
        if self.contradict:
            return
        K = len(remain) 
        while remain:
            var = self.siguientep(remain)
            remain.remove(var)
            list = self.get(var)
            if verb:
                print("analizando variable ", var, "quedan ", len(remain))
            
            if len(list) == 0:
                if verb:
                    print("borrando variable no potential", var)
                self.orden.append(var)
                self.posvar[var] = len(self.orden) - 1
                self.compiled[var] = nodoTabla([])
                self.det[var] = False

            elif len(list) == 1:
                if verb:
                    print("borrando variable one potential", var)
                p = list[0]
                self.eliminar(p)
                self.orden.append(var)
                self.posvar[var] = len(self.orden) - 1
                h = p.borra([var], inplace=False)    
                self.insertar(h)
                if var in p.det or p.checkdetermi(var):
                    pot = p.minimizadep(var)
                    self.det[var] = True
                    self.compiled[var] = pot
                    if verb:
                        print("determinismo ", p.getvars(), pot.getvars())
                else:
                    old = len(p.getvars())
                    p = p.minimiza(h)
                    new = len(p.getvars())
                    if new < old and verb:
                        print("minimizo *********--------------->", new, old)
                    self.compiled[var] = p
                    self.det[var] = False
            else:
                ok = self.borrasidet(var, len(remain), verb=verb)
                if not ok:
                    ok = self.compilevar(var, nondet=True, test=test, wait=True, verb=verb)

    def borrasidet(self, var, K, verb=True):
        list = self.get(var)
        for q in list:
            self.eliminar(q)
        d = False
        u.improve(list)
        u.agrupatam(list)
        for q in list:
            self.insertar(q)
        list = self.get(var)
        for p in list:
            if var in p.det or p.checkdetermi(var):
                d = True
                for q in list:
                    self.eliminar(q)
                pot = p.minimizadep(var)

                if self.tadref(pot, list) <= self.Q:
                    if verb:
                        print("borrando deterministic ", var, " quedan ", K)
                    if len(list) == 1:
                        h = p.borra([var], inplace=False)
                        self.insertar(h)
                    else:
                        if pot == p and len(list) > 1:
                            list.remove(p)
                        u.combinasize(list, pot, self.Q)
                        for q in list:
                            h = pot.combina(q, inplace=False).borra([var], inplace=False)
                            self.insertar(h)
                    self.orden.append(var)
                    self.posvar[var] = len(self.orden) - 1
                    self.det[var] = True
                    self.compiled[var] = pot
                    break
                else:
                    if pot == p and len(list) > 1:
                        list.remove(p)
                    u.combinasize(list, pot, self.Q)
                    refs = set(pot.getvars())
                    for q in list:
                        if len(refs.union(set(q.getvars()))) <= self.Q:
                            h = pot.combina(q, inplace=False).borra([var], inplace=False)
                            self.insertar(h)
                        else:
                            if verb:
                                print("******* reservando un potencial determinista ")
                            if var not in self.wait:
                                self.wait[var] = [q]
                            else:
                                self.wait[var].append(q)
                            if self.A == -1:
                                self.A = len(self.orden)
                    self.orden.append(var)
                    self.posvar[var] = len(self.orden) - 1
                    self.det[var] = True
                    self.compiled[var] = pot
                    break
        return d

    def moreinforma(self, lista):
        lista2 = lista.copy()
        del lista[:]
        total = set()
        p = min(lista2, key=lambda x: (x.tabla.sum().item() if isinstance(x.tabla, torch.Tensor) else int(x.tabla)) / (2**len(x.getvars())))
        lista2.remove(p)
        lista.append(p)
        total.update(set(p.getvars()))
        while lista2:
            p = min(lista2, key=lambda x: len(total.union(set(x.getvars()))))
            if len(total.union(set(p.getvars()))) > self.Q:
                break
            else:
                total.update(set(p.getvars()))
                lista2.remove(p)
                lista.append(p)
        return lista2
        
    def minil(self, lista, var):
        wl = lista.copy()
        while wl:
            l2 = self.moreinforma(wl)
            q = nodoTabla([])
            for p in wl:
                q = q.combina(p)
            if var in q.getvars():
                h = q.borra([var], inplace=False)
                self.insertar(h)
            wl = l2

    def compilevar(self, var, nondet=False, wait=False, test=True, verb=True):
        list = self.get(var)
        size = computesize(list)
        su = False
        if size > self.Q and not wait:
            return False
        for p in list:
            self.eliminar(p)
        if size > self.Q and wait:
            list2 = self.moreinforma(list)
            if list2:
                if self.A == -1:
                    self.A = len(self.orden)
                if verb:
                    print("reservando variable ********************* ", var, len(list2))
                self.wait[var] = list2

        size = computesize(list)
        if verb:
            print(size, len(list))
        if size <= self.Q and list:
            if len(list) == 1:
                p = list[0]
            else:
                p = nodoTabla([])
                for q in list:
                    p = p.combina(q)
            
            if var in p.det or p.checkdetermi(var):
                self.borradetl(var, p, list, verb=verb)
            elif nondet:
                if test and self.A == -1:
                    if verb:
                        print("Comprobando ")
                    r = p.computedet(var)
                    if verb:
                        r_sum = r.tabla.sum().item() if isinstance(r.tabla, torch.Tensor) else int(r.tabla)
                        print("No determinismo ", r_sum / 2**(len(r.getvars())))
                    nuevo = self.copia()
                    nuevo.insertar(r)
                    nuevo.orden.append(var)
                    nuevo.posvar[var] = len(self.orden) - 1
                    nuevo.det[var] = False
                    nuevo.Q = max(self.Q, 25)
                    nuevo.compiletotal(verb=False, test=False)
                    if nuevo.contradict:
                        if verb:
                            print("SII exito ")
                        p = p.combina(r.neg())
                        self.borradetl(var, p, list, verb=verb)
                        return
                    elif verb:
                        print("NOO exito ")

                h = p.borra([var], inplace=False)
                self.orden.append(var)
                self.posvar[var] = len(self.orden) - 1
                self.det[var] = False
                old = len(p.getvars())
                p = p.minimiza(h)
                new = len(p.getvars())
                if new < old and verb:
                    print("minimizo *********--------------->", new, old)
                self.compiled[var] = p
                if verb:
                    print("borrando no determinismo")
                self.insertar(h)
                
        elif wait:
            if self.A == -1:
                self.A = len(self.orden)
            if verb:
                print("reservando variable ------------------->", len(list))
            self.wait[var] = list
            self.compiled[var] = nodoTabla([])
            self.orden.append(var)
            self.posvar[var] = len(self.orden) - 1
            self.det[var] = False

        return su

    def borradetl(self, var, p, list, verb=True):
        self.orden.append(var)
        self.posvar[var] = len(self.orden) - 1
        self.det[var] = True
        pot = p.minimizadep(var)
        
        self.compiled[var] = pot
        if verb:
            print(p.getvars(), pot.getvars())
        if not pot == p:
            u.combinasize(list, pot, self.Q)
            for q in list:
                h = pot.combina(q, inplace=False).borra([var], inplace=False)
                self.insertar(h)
        else:
            h = p.borra([var], inplace=False)
            self.insertar(h)

    def recompileupdet(self, K=6, verb=True):
        n = len(self.orden)
        for i in range(n - 1, -1, -1):
            v = self.orden[i]
            lv = set(self.compiled[v].getvars())
            if self.det[v] and len(lv) <= K:
                for j in range(i):
                    w = self.orden[j]
                    if lv <= set(self.compiled[w].getvars()):
                        self.compiled[w] = self.compiled[w].combina(self.compiled[v]).borra([v], inplace=False)
                        print("reducción quito ", v, "de ", self.compiled[w].getvars())

    def tocont(self):
        for i in range(len(self.orden) - 1, self.A - 1, -1):
            v = self.orden[i]
            self.compiled[v] = [self.compiled[v]]
        self.tocont = True

    def insertarc(self, p):
        if p.tabla.trivial():
            return
        tvars = p.getvars() + [abs(x) for x in p.context] 
        po = min(self.posvar[v] for v in tvars)
        w = self.orden[po]
        filt = [q for q in self.compiled[w] if p.compatible(q)]

        tamm = max([len((set(q.getvars()) - {abs(x) for x in p.context}).union(set(p.getvars()) - {abs(x) for x in q.context})) for q in filt])

        if tamm > self.Q:
            w = next((item for item in self.varcontext if item in p.getvars()), -1)
            if w == -1:
                w = min(p.getvars(), key=lambda x: x.entropia())
            (pot1, pot2) = p.split(w)
            self.insertarc(pot1)
            self.insertarc(pot2)
        else:
            if w in p.context or -w in p.context:
                p = p.uncontext(w)
            filtd = list(filter(lambda x: w in x.tabla.det, filt))
            filtnd = [q for q in filt if q not in filtd]

            full = list(filter(lambda x: x.context <= p.context, filt))
            if full:
                piv = full[0]
                h = piv.combina(p).borra([w], inplace=False)
                self.insertarc(h)
            else:
                f = False
                for q in filt:
                    h = q.combina(p).borra([w], inplace=False)
                    self.insertarc(h)
                    if q.context == p.context and computesize([p, q]) <= self.Q and not f:
                        f = True
                        h = q.combina(p)
                        self.compiled[w].remove(q)
                        self.compiled[w].append(h)
                if not f:
                    self.compiled[w].append(p)

    def getInitial(self):
        config = self.unit.copy()
        
        for v in self.orden[::-1]:
            p = self.compiled[v]
            q = p.reduce(config)
            if v in self.wait:
                for pw in self.wait[v]:
                    q = q.combina(pw.reduce(config))

            if not q.getvars():
                print("no determinado ")
                config.add(choice([v, -v]))
            elif not bool(q.tabla[0]) and bool(q.tabla[1]):
                config.add(v)
            elif bool(q.tabla[0]) and not bool(q.tabla[1]):
                config.add(-v)
            else:
                print("no determinado ")
                config.add(choice([v, -v]))
        return config

    def markovchainlogic(self):
        remain = self.orden[self.A:].copy()
        list = self.getpotl(remain)
        npot = len(list)

        config = self.getInitial()
        print(config)

        lsat = [bool(p.getvalue(config)) for p in list]
        nsat = sum(lsat)
        print(nsat, npot)
        changes = True
        while nsat < npot and changes:
            changes = False
            for v in remain:
                listv = getl(list, {v})
                if v in config:
                    old = v
                else:
                    old = -v
                nold = sum([bool(p.getvalue(config)) for p in listv])
                config.remove(old)
                config.add(-old)
                nnew = sum([bool(p.getvalue(config)) for p in listv])
                if nnew > nold:
                    changes = True
                    nsat = nnew - nold + nsat
                    print("mejora", nsat, npot)
                else:
                    config.remove(-old)
                    config.add(old)
        return config

    def markovchainvar(self, config, i=2):
        remain = self.orden[self.A:].copy()
        lista = self.getpotl(remain)
        npot = len(lista)

        lsat = [bool(p.getvalue(config)) for p in lista]
        nsat = sum(lsat)

        setsi = self.computesets(lista, i=i)

        changes = True
        while changes and nsat < npot:
            changes = False
            for s in setsi:
                ch = [{x, -x} for x in s]
                
                listv = getl(lista, s)
                nold = sum([bool(p.getvalue(config)) for p in listv])
                oldconf = set()
                mvalue = nold
                
                for x in s:
                    if x in config:
                        oldconf.add(x)
                        config.remove(x)
                    else:
                        oldconf.add(-x)
                        config.remove(-x)
                conm = oldconf
                for c in product(*ch):
                    newconf = set(c)
                    config.update(newconf)
                    nnew = sum([bool(p.getvalue(config)) for p in listv])
                    if nnew > mvalue:
                        nsat = nsat + nnew - mvalue
                        mvalue = nnew
                        print("Mejora", nsat, npot, i)
                        changes = True
                        conm = newconf
                    config = config - newconf
                config.update(conm)
                
        return config

    def computesets(self, lista, i=2):
        listsets = []
        for p in lista:
            h = p.getvars()
            l = combinations(h, i)
            for x in l:
                if x not in listsets:
                    listsets.append(x)
        return listsets

    def npotentials(self):
        return len(self.getpotl())

    def siguientep(self, pos):
        for x in pos:
            lista = self.tablas.get(x)
            x1 = len(lista) if self.tablas.get(x) else 0
            if x1 <= 1:
                return x
            
        for x in pos:
            lista = self.tablas.get(x)
            lred = [p for p in lista if x in p.det]
            if lred:
                mp = min(lred,key = lambda x : len(x.getvars()))
                if len(mp.getvars()) == 2:
                    return x

        
        miv = min(pos, key=lambda x: self.tadm(x))
        return miv


    def choose(self, pos):
        
        miv = max(pos, key=lambda x: self.tadm(x))
        return miv
    

    def borrav(self, var):
        lista = []
        if self.contradict:
            print("contradiction ")
            return
        if var in self.unit:
            self.unit.discard(var)
            return (True, lista, [u.potdev(var)])
        elif -var in self.unit:
            self.unit.discard(-var) 
            return (True, lista, [u.potdev(-var)])

        (exact, lista, listaconvar) = u.marginaliza(self.get(var).copy(), var, self.partir, M, Q)
        
        if exact and lista and not lista[0].getvars():
            if lista[0].contradict():
                print("contradict")
                self.anula()    
                return (True, lista, listaconvar)
        for p in lista:
            if p.contradict():
                print("contradict")
                self.anula()
            else:
                self.insertar(p)     

        self.borrarv(var)
        return (exact, lista, listaconvar)

    def insertbay(self, p):
        if not p.getvars():
            print("sin variables ")
            val = p.tabla.item() if isinstance(p.tabla, torch.Tensor) else p.tabla
            self.w = self.w * val
            print(self.w)
        for v in p.getvars():
            if v in self.prob:
                self.prob[v].append(p)
            else:
                self.prob[v] = [p]
        
    def removebay(self, p):    
        for v in p.getvars():
            self.prob[v].remove(p)

    def getpot(self, L=5):
        res = []
        for v in self.tabla:
            for p in self.tabla[v]:
                if len(p.getvars()) >= L and p not in res:
                    res.append(p)
        for v in self.tablach:
            for p in self.tablach[v]:
                if len(p.getvars()) >= L and p not in res:
                    res.append(p)
        return res

    def getpotl(self, l):
        res = []
        for v in l:
            res.append(self.compiled[v])
            if v in self.wait:
                res = res + self.wait[v]
        return res

    def getvarsd(self, v):
        res = set()
        l = self.get(v) + self.getd(v)
        for p in l:
            res.update(set(p.getvars()))
        return res

    def copia(self):
        res = varpot()
        if self.contradict:
            res.contradict = True
            return res
        for v in self.tablas:
            res.tablas[v] = self.tablas[v].copy()

        for v in self.tablam:
            res.tablam[v] = self.tablam[v].copy()

        res.svars = self.svars.copy()
    
        for v in self.prob:
            res.prob[v] = self.prob[v].copy()

        res.orden = self.orden.copy()
        res.posvar = self.posvar.copy()
        res.w = self.w
        res.Q = self.Q
        res.A = self.A

        if self.compiled:
            res.compiled = self.compiled.copy()
        
        return res

    def level(self, p):
        return min([self.posvar[x] for x in p.getvars()])

    def levelc(self, cl):
        return min([self.posvar[abs(x)] for x in cl])
    
    def back(self):
        vars = self.orden.copy()
        level = len(vars) - 1
        config = []
        while level > 0:
            oldl = level
            print(level, len(config), level + len(config), config)
            var = self.orden[level]
            list1 = []
            list2 = []
            lista = self.get(var) + self.getd(var) + self.getm(var)
            margi = False
            for p in lista:
                t = p.reduce(config)
                if t.contradict():
                    nueva = p.borra([var])
                    self.insertarb(nueva)
                    level = self.level(nueva)
                    del config[-(level - oldl):]
                    margi = True
                    break   
                elif not bool(t.tabla[0]):
                    list1.append(p)
                elif not bool(t.tabla[1]):
                    list2.append(p)
            if margi:
                continue
            
            if not list2:
                config.append(var)
                level += -1
                continue
            if not list1:
                config.append(-var)
                level += -1
                continue

            n1 = min(list1, key=lambda x: len(x.getvars()))
            n2 = min(list2, key=lambda x: len(set(x.getvars()).union(set(n1.getvars()))))

            nueva = n1.combina(n2, inplace=False)
            nueva.borra([var], inplace=True)
            self.insertarb(nueva)
            level = self.level(nueva)
            del config[-(level - oldl):]

    def belong(self, p):
        h = p.getvars()
        if not h:
            return False
        v = h[0]
        if v in self.tabla and p in self.tabla[v]:
            return True
        if v in self.tablach and p in self.tablach[v]:
            return True
        return False
                
    def back2(self, Q=15):
        vars = self.getvars()
        pos = list(vars)
        orden = []
        level = len(vars) - 1
        config = []
        while level > 0:
            oldl = level
            (var, apren) = self.siguienteb(config, pos)
            print(level, len(config), var, config)

            self.posvar[abs(var)] = level
            pos.remove(abs(var))
            orden.append(abs(var))

            if apren:
                sets = []
                for nueva in apren:
                    print("aprendo ", nueva.getvars())
                    sets = sets + self.insertback(nueva)
                if self.contradict:
                    break
                for h in sets:
                    level = max(level, self.level(h))
                pos = pos + orden[-(level - oldl) - 1:]
                del orden[-(level - oldl) - 1:]
                del config[-(level - oldl):]
            else:
                config.append(var)
                level += -1
        return config 

    def compruebasol(self, config):
        vars = self.getvars()
        for v in vars:
            lista = self.get(v) + self.getd(v)
            for p in lista:
                h = p.reduce(config, inplace=False)
                if not h.trivial():
                    print("error ", p.getvars())

    def trivial(self):
        if self.tabla:
            for v in self.tabla:
                if self.tabla[v]:
                    return False
        if self.tablach:
            for v in self.tablach:
                if self.tablach[v]:
                    return False
        return True

    def reduce(self, v):
        res = self.copia()
        res.insertvar(v)
        return res
        
    def tosecond(self):
        self.second = True
        for v in self.compiled:
            self.compiled[v] = [self.compiled[v]]    

    def insertarclau(self, cl):
        if len(cl) <= 10:
            vars = list(map(abs, cl))
            p = nodoTabla(vars)
            p.introduceclaun(cl)
            return self.insertarb2(p)
        
        if not cl:
            self.anula()
            return []

        svar = set(map(abs, cl))
        lcl = list(cl)

        for v in svar:
            if v in self.tablach:
                for q in self.tablach[v]:
                    if set(q.getvars()) <= svar:
                        if q.getvalue(lcl):
                            ncl = cl - {v, -v}
                            return self.insertarclau(ncl)

            if v in self.clau:
                for d in self.clau[v]:
                    if d <= cl:
                        return []
                    if v in cl:
                        ncl = d - {v}
                        ncl.add(-v)
                        if ncl <= cl:
                            cl.discard(v)
                            return self.insertarclau(cl)
                    if -v in cl:
                        ncl = d - {-v}
                        ncl.add(v)
                        if ncl <= cl:
                            cl.discard(-v)
                            return self.insertarclau(cl)

        lista = []
        for v in svar:
            if v in self.tablach:
                for q in self.tablach[v]:
                    if q not in lista:
                        lista.append(q)
            if v in self.tabla: 
                for q in self.tabla[v]:
                    if q not in lista:
                        lista.append(q)
            
        for q in lista:
            if svar <= set(q.getvars()):
                q.introduceclaun(cl)    

        ins = []  
        res = [map(abs, cl)]                
        for v in svar:
            if v in self.clau:
                for d in self.clau[v]:
                    if v == min(svar) and cl <= d:
                        self.eliminarc(d)
                    if v in d:
                        ncl = d - {v}
                        ncl.add(-v)
                        if cl <= ncl:
                            ncl.discard(-v)
                            ins.append(ncl)
                            self.eliminarc(d)

                    if -v in d:
                        ncl = d - {-v}
                        ncl.add(v)
                        if cl <= ncl:
                            ncl.discard(v)
                            ins.append(ncl)
                            self.eliminarc(d)
                
        for d in ins:
            res = res + self.insertarclau(d)

        for v in svar:
            if v in self.clau:
                self.clau[v].append(cl)
            else:
                self.clau[v] = [cl]

        return res

    def eliminarb(self, p):
        i = self.level(p)
        var = self.orden[i]
        if p in self.get(var):
            self.tabla[var].remove(p)
        if p in self.getd(var):
            self.tablach[var].remove(p)

        for v in p.getvars():
            self.tablat[v].remove(p)

    def checkequal(self, p):
        svars = p.getvars()
        if not svars:
            return p
        if svars[0] in self.tablas:
            lista = self.tablas[svars[0]].copy()
        else:
            return p
                        
        for q in lista:
            if set(q.getvars()) == set(svars):
                self.eliminar(q)
                return p.combina(q)
        return p

    def eliminarc(self, cl):
        lvar = map(abs, cl)
        for v in lvar:
            self.clau[v].remove(cl)

    def createfromlista(self, l):
        for p in l:
            self.insertar(p)

    def siguiente(self):
        if self.unit:
            x = self.unit.pop()
            self.unit.add(x)
            return abs(x)
        miv = min(self.tabla, key=lambda x: len(self.tabla.get(x)))
        if len(self.tabla.get(miv)) == 1:
            return miv
        miv = min(self.tabla, key=lambda x: tam(self.tabla.get(x)))
        return miv

    def getmax(self, proh=set()):
        pos = set(self.getvars()) - proh
        bue = dict()
        for x in pos:
            bue[x] = 0.0
        
        for v in self.getvars():
            if v in self.tablach:
                for p in self.tablach[v]:
                    n = len(p.getvars())
                    for y in p.getvars():
                        bue[y] += 1 / n
        return max(bue, key=bue.get)

    def marginalizae(self, var, M=20):
        lista = []
        if self.contradict:
            return (True, lista, [])
        if var in self.unit:
            self.unit.discard(var)
            return (True, lista, [u.potdev(var)])
        elif -var in self.unit:
            self.unit.discard(-var) 
            return (True, lista, [u.potdev(-var)])

        (exact, lista, listaconvar, unit) = u.marginalizas(self.get(var).copy(), var, self.partir, M)
        if 0 in unit:
            self.anula()
            return (True, lista, listaconvar)
        
        if exact and lista and not lista[0].getvars():
            if lista[0].contradict():
                self.anula()    
                return (True, lista, listaconvar)
        if exact:
            for p in lista:
                self.insertar(p)     
            self.borrarv(var)
                    
        return (exact, lista, listaconvar)

    def progresa(self):
        for v in self.orden:
            if v in self.tablach:
                ins = []
                bor = []
                for p in self.tablach[v]:
                    if v in self.tabla:
                        for q in self.tabla[v]:
                            dif = set(p.getvars()) - set(q.getvars())
                            if len(dif) == 1:
                                z = dif.pop()
                                if self.varpos[v] < self.varpos[z]:
                                    bor.append(q)
                                    r = p.combina(q, inplace=False)
                                    r.borra([v], inplace=True)
                                    ins.append(r)
                for p in bor:
                    self.eliminar(p)
                for q in ins:
                    self.insertar(q)

    def esta(self, p):
        if not p.getvars():
            if p.trivial():
                return False
            if p.contradict() and self.contradict:
                return True
            else:
                return False

        v = p.getvars()[0]
        if v in self.tabla and p in self.tabla[v]:
            return True
        if v in self.tablach and p in self.tablach[v]:
            return True
        return False

    def estad(self, p):
        if not p.getvars():
            if p.trivial():
                return False
            if p.contradict() and self.contradict:
                return True
            else:
                return False
        
        for v in p.getvars():
            if p in self.tablach.get(v, []):
                return True
        return False

    def pos(self, p):
        return min([self.posvar[x] for x in p.getvars()])

    def extraelista(self):
        lista = []
        for v in self.tabla:
            for p in self.tabla[v]:
                if min(p.getvars()) == v:
                    lista.append(p)
        return lista

    def tadm(self, v):
        mat = 0
        d = False
        if v in self.tablas:
            for q in self.tablas[v]:
                if v in q.det:
                    piv = q
                    d = True
                    break
        
        if d:
            sset = set(piv.getvars())
            for q in self.tablas[v]:
                mat += 2**(len(sset.union(set(q.getvars())))) - 2**(len(q.getvars()))
            return mat

        sset = set()
        if v in self.tablas:
            for q in self.tablas[v]:
                sset.update(set(q.getvars()))
                mat += - 2**(len(q.getvars()))

        return (mat + 2**(len(sset) - 2))

    def tadref(self, pot, list):
        svars = set(pot.getvars())
        return max([len(svars.union(set(x.getvars()))) for x in list], default=0)

    def siguientepref(self, pos, small):
        for x in pos:
            x1 = len(self.tabla.get(x)) if self.tabla.get(x) else 0
            x2 = len(self.tablach.get(x)) if self.tablach.get(x) else 0
            if x1 + x2 <= 1:
                return x

        miv = min(pos, key=lambda x: min(self.tadref(x, small, pos), self.tad(x)))
        return miv   

    def get(self, i):
        return self.tablas.get(i, []).copy()

    def getl(self, l):
        li = []
        for i in l:
            for x in self.tablas.get(i, []) + self.tablasch.get(i, []):
                if x not in li:
                    li.append(x)
        return li
        
    def getm(self, i, deep=True):
        if deep:
            return self.tablasm.get(i, []).copy()
        else:
            return self.tablasm.get(i, [])

    def mini(self, vorig, small, Q, trabajo, gorden=[], verb=True, M=3, H=40):
        clusters = []
        posvar = dict()
        solved = True
        orden = []
        horden = gorden.copy()
        horden.reverse()
        cset = set()
        pd = 0
        pnd = 0

        while vorig and not trabajo.contradict:
            if len(vorig) > H:
                QV = Q
            else:
                QV = 31

            if gorden:
                var = horden.pop()
            else:
                var = trabajo.siguientepref(vorig, small)
            lset = cset.union(self.getvarsd(var))
            clusters.append(lset - cset)
            cset = lset
            
            if verb:
                print("var", var, "quedan ", len(vorig))
            orden.append(var)
            posvar[var] = len(orden) - 1

            list1 = trabajo.get(var)
            list2 = trabajo.getd(var)

            x1 = trabajo.tadref(var, small, vorig)
            x2 = trabajo.tad(var)

            if verb:
                print(x1, x2)
                print(len(list1), len(list2))

            for p in list1:
                trabajo.eliminar(p)
            for p in list2:
                trabajo.eliminar(p)

            n = len(list1) + len(list2)
            nd = []
            traba = []
            nuevas = []
            if x1 < x2:
                if verb:
                    print("incluir ")
                lists = small.tablach.get(var, [])
                lists2 = list(filter(lambda x: set(x.getvars()) <= set(vorig), lists))
                if lists2:
                    if verb:
                        print("heredo determinismo", len(list1))
                    p = min(lists2, key=lambda x: len(x.getvars()))
                    list2.append(p)

            vorig.discard(var)

            if list2:
                if verb:
                    print("determinista")
                pd += 1
                pivote = min(list2, key=lambda x: len(x.getvars()))
                if n <= 1:
                    h = pivote.borra([var], inplace=False)
                    (h, l1) = trabajo.simplificat(h)
                    (h, l1) = small.simplificat(h)
                    nd = nd + trabajo.insertar(h, small)
                    nuevas.append(h)
                    for r in l1:
                        nd = nd + trabajo.insertar(h, small)
                else:
                    for p in list1:
                        pivote = min(list2, key=lambda x: len(set(p.getvars()).union(set(x.getvars()))))
                        if len(set(p.getvars()).union(set(pivote.getvars()))) <= QV:
                            h = pivote.combina(p, inplace=False)
                            h.borra([var], inplace=True)
                            (h, l1) = trabajo.simplificat(h)
                            (h, l1) = small.simplificat(h)
                            nd = nd + trabajo.insertar(h, small)
                            nuevas.append(h)
                            for r in l1:
                                nd = nd + trabajo.insertar(r, small)
                        else:
                            traba.append(p)
                    while len(list2) > 1:
                        list2.sort(key=lambda x: len(x.getvars()))
                        p = list2.pop()
                        pivote = min(list2, key=lambda x: len(set(p.getvars()).union(set(x.getvars()))))
                        
                        if len(set(p.getvars()).union(set(pivote.getvars()))) <= QV:
                            h = pivote.combina(p, inplace=False)
                            h.borra([var], inplace=True)
                            (h, l1) = trabajo.simplificat(h)
                            (h, l1) = small.simplificat(h)
                            nd = nd + trabajo.insertar(h, small)
                            nuevas.append(h)
                            for r in l1:
                                nd = nd + trabajo.insertar(r, small)
                        else:
                            traba.append(p)
                            solved = False
                    
                    if traba:
                        for p in traba:
                            h = p.borra([var], inplace=False)
                            (h, l1) = trabajo.simplificat(h)
                            (h, l1) = small.simplificat(h)
                            nd = nd + trabajo.insertar(h, small)
                            nuevas.append(h)
                            for r in l1:
                                nd = nd + trabajo.insertar(r, small)
            else:
                if verb:
                    print("no determinista")
                pnd += 1
                h = nodoTabla([])
                ordena(list1, QV)
                if list1:
                    for q in list1:
                        if len(set(h.getvars()).union(set(q.getvars()))) <= QV or not h.getvars():
                            h.combina(q, inplace=True)
                        else:
                            h.borra([var], inplace=True)
                            nd = nd + trabajo.insertar(h, small)
                            nuevas.append(h)
                            h = nodoTabla([])
                            h.combina(q, inplace=True)

                    h.borra([var], inplace=True)
                    (h, l1) = trabajo.simplificat(h)
                    (h, l1) = small.simplificat(h)
                    nd = nd + trabajo.insertar(h, small)
                    nuevas.append(h)
                    for r in l1:
                        nd = nd + trabajo.insertar(r, small)

            for p in nd:
                small.insertar(p)
                if len(p.getvars()) <= 2:
                    self.insertar(p)

            for p in nuevas:
                if p not in nd and len(p.getvars()) <= M:
                    small.insertar(p, small)
        return (solved, orden)

    def minid2(self, orden, rever, Q):
        for o in (orden, rever):
            vorig = o.copy()
            vorig.reverse()
            trabajo = self.copia()
        
            while vorig and not self.contradict: 
                var = vorig.pop()
                print(var, len(vorig))

                list1 = trabajo.get(var)
                list2 = trabajo.getd(var)

                for p in list1:
                    trabajo.eliminar(p)
                for p in list2:
                    trabajo.eliminar(p)

                n = len(list1) + len(list2)
                nd = []
                traba = []
                nuevas = []

                if list2:
                    pivote = min(list2, key=lambda x: len(x.getvars()))
                    if n <= 1:
                        h = pivote.borra([var], inplace=False)
                        nd = nd + trabajo.insertard(h)
                        nuevas.append(h)
                    else:
                        for p in list1:
                            pivote = min(list2, key=lambda x: len(set(p.getvars()).union(set(x.getvars()))))
                            if len(set(p.getvars()).union(set(pivote.getvars()))) <= Q:
                                h = pivote.combina(p, inplace=False)
                                h.borra([var], inplace=True)
                                nd = nd + trabajo.insertar(h)
                                nuevas.append(h)
                            else:
                                traba.append(p)
                        list2.sort(key=lambda x: len(x.getvars()))

                        while len(list2) > 1:
                            p = list2.pop()
                            pivote = min(list2, key=lambda x: len(set(p.getvars()).union(set(x.getvars()))))
                            if len(set(p.getvars()).union(set(pivote.getvars()))) <= Q:
                                h = pivote.combina(p, inplace=False)
                                h.borra([var], inplace=True)
                                nd = nd + trabajo.insertar(h)
                                nuevas.append(h)
                            else:
                                traba.append(p)
                        
                        if traba:
                            for p in traba:
                                h = p.borra([var], inplace=False)
                                nd = nd + trabajo.insertard(h)
                                nuevas.append(h)
                else:
                    h = nodoTabla([])
                    combinaincluidas(list1, K=1)
                    if list1:
                        for q in list1:
                            if len(set(h.getvars()).union(set(q.getvars()))) <= Q or not h.getvars():
                                h.combina(q, inplace=True)
                            else:
                                h.borra([var], inplace=True)
                                nd = nd + trabajo.insertard(h)
                                nuevas.append(h)
                                h = nodoTabla([])
                                h.combina(q, inplace=True)

                        h.borra([var], inplace=True)
                        nd = nd + trabajo.insertar(h)
                        nuevas.append(h)
                
                for p in nd:
                    self.insertarb2(p)
                for p in nuevas:
                    self.insertarb2(p)
        return 

    def minid(self, Q, ins=True, nue=True):
        vorig = self.orden.copy()
        vorig.reverse()
        orden = []
        posvar = dict()
        trabajo = self.copia()

        print("en orden directo")

        while vorig and not self.contradict: 
            var = vorig.pop()
            orden.append(var)
            posvar[var] = len(orden) - 1

            list1 = trabajo.get(var)
            list2 = trabajo.getd(var)

            for p in list1:
                trabajo.eliminar(p)
            for p in list2:
                trabajo.eliminar(p)

            n = len(list1) + len(list2)
            nd = []
            traba = []
            nuevas = []

            if list2:
                pivote = min(list2, key=lambda x: len(x.getvars()))
                if n <= 1:
                    h = pivote.borra([var], inplace=False)
                    nd = nd + trabajo.insertar(h)
                    if trabajo.contradict:
                        return 
                    nuevas.append(h)
                else:
                    for p in list1:
                        pivote = min(list2, key=lambda x: len(set(p.getvars()).union(set(x.getvars()))))
                        if len(set(p.getvars()).union(set(pivote.getvars()))) <= Q:
                            h = pivote.combina(p, inplace=False)
                            h.borra([var], inplace=True)
                            nd = nd + trabajo.insertar(h)
                            if trabajo.contradict:
                                return
                            nuevas.append(h)
                        else:
                            traba.append(p)
                    list2.sort(key=lambda x: len(x.getvars()))

                    while len(list2) > 1:
                        p = list2.pop()
                        pivote = min(list2, key=lambda x: len(set(p.getvars()).union(set(x.getvars()))))
                        if len(set(p.getvars()).union(set(pivote.getvars()))) <= Q:
                            h = pivote.combina(p, inplace=False)
                            h.borra([var], inplace=True)
                            nd = nd + trabajo.insertar(h)
                            if trabajo.contradict:
                                return
                            nuevas.append(h)
                        else:
                            traba.append(p)
                    
                    if traba:
                        for p in traba:
                            h = p.borra([var], inplace=False)
                            if trabajo.contradict:
                                return
                            nd = nd + trabajo.insertar(h)
                            nuevas.append(h)

            elif list1:
                h = nodoTabla([])
                combinaincluidas(list1, K=1)
            
                for q in list1:
                    if len(set(h.getvars()).union(set(q.getvars()))) <= Q or not h.getvars():
                        h = h.combina(q)
                    else:
                        h.borra([var], inplace=True)
                        nd = nd + trabajo.insertar(h)
                        if trabajo.contradict:
                            return 
                        nuevas.append(h)
                        h = nodoTabla([])
                        h.combina(q, inplace=True)

                h.borra([var], inplace=True)
                nd = nd + trabajo.insertar(h)
                nuevas.append(h)
                       
            if ins:
                for p in nd:
                    if len(p.getvars()) <= 15:
                        print("nuevo determinismo", p.getvars())
                        self.insertar(p)
            
            if nue:
                for p in nuevas:
                    if len(p.getvars()) <= 5:
                        self.insertar(p)
                    else:
                        self.simplify(p)

                    if self.contradict:
                        return 
        return 

    def simplifyp(self, t):
        lista = self.getpotl(self.getvars())
        for p in lista:
            n = len(p.getvars())
            svar = set(p.getvars())
            op = p.tabla.sum().item() if isinstance(p.tabla, torch.Tensor) else int(p.tabla)
            for v in p.getvars():
                if v in t.tabla:
                    for q in t.tabla[v]:
                        if len(q.getvars()) <= n and set(q.getvars()) <= svar:
                            p.combina(q, inplace=True)
                if v in t.tablach:
                    for q in t.tablach[v]:
                        if len(q.getvars()) <= n and set(q.getvars()) <= svar:
                            p.combina(q, inplace=True)

            np_val = p.tabla.sum().item() if isinstance(p.tabla, torch.Tensor) else int(p.tabla)
            print(op, np_val, n)

    def localimprove(self, Q=25):
        lista = self.getpot(L=Q)
        print(len(lista))
        sleep(3)
        i = 0
        for p in lista:
            i += 1
            print(i)
            if not self.belong(p):
                continue
            work = self.copia()

            vorig = set(work.getvars()) - set(p.getvars())
            while vorig and not self.contradict: 
                var = work.siguientep(vorig)
                vorig.discard(var)
                list1 = work.get(var)
                list2 = work.getd(var)
                h = nodoTabla([])
                for q in list1:
                    if len(set(h.getvars()).union(set(q.getvars()))) <= 25:
                        h = h.combina(q)
                    else:
                        r = q.borra([var])
                        work.insertar(r)
                    work.eliminar(q)
                for q in list2:
                    if len(set(h.getvars()).union(set(q.getvars()))) <= 25:
                        h = h.combina(q)
                    else:
                        r = q.borra([var])
                        work.insertar(r)
                    work.eliminar(q)
                if not h.trivial():
                    h = h.borra([var])
                    work.insertar(h)

            listf = work.getpot(0)
            h = nodoTabla([])
            for q in listf:
                h = h.combina(q)

            p_sum = p.tabla.sum().item() if isinstance(p.tabla, torch.Tensor) else int(p.tabla)
            h_sum = h.tabla.sum().item() if isinstance(h.tabla, torch.Tensor) else int(h.tabla)
            print(p_sum, h_sum, 2**(len(p.getvars())))
            sleep(1)

            if not h.implicadopor(p):
                print("mejora")
                self.eliminar(p)
                self.insertar(h)

    def checkincluded(self):
        lista = self.getpotl(self.getvars())        
        lista.sort(key=lambda x: -len(x.getvars()))

        i = 0
        while i < len(lista) - 1:
            j = i + 1
            while j < len(lista):
                if set(lista[j].getvars()) <= set(lista[i].getvars()):
                    p = lista[i]
                    q = lista[j]
                    self.eliminar(q)
                    self.eliminar(p)
                    t = p.combina(q)
                    self.insertar(t)
                    print("algo no va bien")
                    sleep(1)
                    lista[i] = t
                    lista.remove(q)
                else:
                    j += 1
            i += 1
        
    def minentr(self):
        ent = dict()
        pos = dict()
        neg = dict()
        lista = self.getvars()
        lp = self.getpotl(lista)
        for v in lista:
            pos[v] = 1
            neg[v] = 1 
        for p in lp:
            for v in p.getvars():
                (x0, x1) = p.cuenta(v)
                pos[v] *= x0
                neg[v] *= x1
                s = pos[v] + neg[v]
                pos[v] = pos[v] / s
                neg[v] = neg[v] / s

        for v in lista:
            x0 = pos[v]
            x1 = neg[v]
            if x0 == 0 or x1 == 0:
                ent[v] = 0
            else:
                ent[v] = -x0 * math.log(x0) - x1 * math.log(x1)  
            print(ent[v])

        return min(ent, key=ent.get)

    def borrac(self, Q, conf=[]):
        print(conf)
        print("entro en borraf")
        self.borraf(Q=Q)
        print("salgo de borraf")

        if self.contradict:
            return 

        lvars = self.getvars()
        if not lvars:
            return
        print(len(lvars))
        count = dict()
        for x in lvars:
            count[x] = 0

        lpot = self.getpotl(lvars)

        for p in lpot:
            for z in p.getvars():
                if p in self.tablach.get(z, []):
                    count[z] += 3
                else:
                    count[z] += 1

        var = max(count, key=count.get)
        print(var)
        conf.append(-var)
        n1 = self.reduce(-var)
        n1.borrac(Q=Q, conf=conf)
        conf.pop()
        conf.append(var)

        n2 = self.reduce(var)
        n2.borrac(Q=Q, conf=conf)
        conf.pop()

    def compileg(self, Q):
        vorig = self.getvars()
        trabajo = self
        res = varpot()
        res.orden = self.orden.copy()
        this = []
        
        while vorig and not trabajo.contradict: 
            var = trabajo.siguientep(vorig)
            i = self.orden.index(var)
            print("var ", var, i, len(vorig), trabajo.tad(var))
            this.append(var)

            list1 = trabajo.get(var)
            list2 = trabajo.getd(var)
            print(len(list1), len(list2))

            for p in list1:
                trabajo.eliminar(p)
            for p in list2:
                trabajo.eliminar(p)  

            vorig.discard(var)
            del self.orden[i]

            n = len(list1) + len(list2)
            list1.sort(key=lambda x: len(x.getvars()))

            if not list2 and n > 2:
                for p in list1:
                    if p.checkdetermi(var):
                        list1.remove(p)
                        list2.append(p)
                        print("nuevo")
                        break
            for p in list1.copy():
                if n == 1:
                    break
                l = p.descomponev(var)
                if len(l) > 1:
                    print(len(p.getvars()), len(l[0].getvars()), len(l[1].getvars()))
                    trabajo.insertar(l[1])
                    list1.remove(p)
                    if not l[0].trivial():
                        list1.append(l[0])

            if list2:
                print("determinista")
                pivote = min(list2, key=lambda x: len(x.getvars()))
                svar = set(pivote.getvars())
                res.insertars(pivote)
                if n <= 1:
                    h = pivote.borra([var], inplace=False)
                    trabajo.insertar(h)
                else:
                    for p in list1:
                        if len(svar.union(set(p.getvars()))) <= Q:
                            h = pivote.combina(p)
                            h = h.borra([var])
                            trabajo.insertar(h)
                        else:
                            h = p.borra([var])
                            trabajo.insertar(h)
                            res.insertar(p)
                            print("no exacto")
                        if trabajo.contradict:
                            break

                    list2.remove(pivote)

                    for p in list2:
                        if len(svar.union(set(p.getvars()))) <= Q:
                            h = pivote.combina(p)
                            h = h.borra([var])
                            trabajo.insertar(h)
                        else:
                            h = p.borra([var])
                            trabajo.insertar(h)
                            res.insertar(p)
                            print("no exacto")

                        if trabajo.contradict:
                            break

            elif list1:
                h = nodoTabla([])        
                for r in list1:
                    if not h.getvars() or len(set(h.getvars()).union(set(r.getvars()))) <= Q:
                        h = h.combina(r)
                    else:
                        print("no exacto")
                        res.insertar(h)
                        h = h.borra([var])
                        trabajo.insertar(h)
                        if trabajo.contradict:
                            break
                        h = r.copia()

                res.insertar(h)
                h = h.borra([var])
                trabajo.insertar(h)
                if trabajo.contradict:
                    break

        if self.contradict:
            print("contradict")
            res.anula()
        
        res.orden = this
        self.orden = res.orden
        self.tabla = res.tabla
        self.tablach = res.tablach
        self.contradict = res.contradict

    def borraf(self, Q, xor=None):
        vorig = self.getvars()
        trabajo = self
        res = varpot()
        res.orden = self.orden.copy()
        msize = 0
        torden = []
        
        while vorig and not trabajo.contradict: 
            if not self.orden:
                var = trabajo.siguientep(vorig)
            else:
                var = trabajo.orden[0]
            i = self.orden.index(var)

            list1 = trabajo.get(var)
            list2 = trabajo.getd(var)
            list3 = trabajo.getm(var)

            for p in list1:
                trabajo.eliminar(p)
            for p in list2:
                trabajo.eliminar(p)   
            for p in list3:
                trabajo.eliminar(p)           
         
            torden.append(var)
            vorig.discard(var)
            del self.orden[i]

            n = len(list1) + len(list2) + len(list3)
            list1.sort(key=lambda x: len(x.getvars()))

            if n > 1:
                nl = list1.copy()
                list1 = []
                for p in nl:
                    l = p.descomponev(var)
                    if len(l) > 1:
                        self.insertar(l[1])
                        if not l[0].trivial():
                            list1.append(l[0])
                    else:
                        list1.append(p)
            if not list2 and len(list1) > 1:
                s = nodoTabla([])
                for p in list1:
                    s = s.combina(p)
                list1 = [s]

            if list2:
                pivote = min(list2, key=lambda x: len(x.getvars()))
                res.insertars(pivote)
                if len(list1) + len(list2) + len(list3) <= 1:
                    h = pivote.borra([var], inplace=False)
                    msize = max(msize, len(pivote.getvars()))
                    trabajo.insertar(h)
                else:
                    for p in list1:
                        pivote = min(list2, key=lambda x: len(set(p.getvars()).union(set(x.getvars()))))
                        if len(set(p.getvars()).union(set(pivote.getvars()))) <= Q:
                            h = pivote.combina(p)
                            msize = max(msize, len(h.getvars()))
                            h = h.borra([var])
                            trabajo.insertar(h)
                        else:
                            h = pivote.resolution(p, var)
                            trabajo.insertar(h[0])
                            trabajo.insertar(h[1])
                            r = p.borra([var])
                            msize = max(msize, len(h[0].getvars()), len(h[1].getvars()), len(r.getvars()))
                            trabajo.insertar(r)
                        
                        if trabajo.contradict:
                            break
                    
                    for p in list3:
                        pivote = min(list2, key=lambda x: len(set(p.getvars()).union(set(x.getvars()))))
                        h = pivote.resolution(p, var)
                        trabajo.insertar(h[0])
                        trabajo.insertar(h[1])
                        r = p.borra([var])
                        trabajo.insertar(r)
                        msize = max(msize, len(h[0].getvars()), len(h[1].getvars()), len(r.getvars()))

                        if trabajo.contradict:
                            break

                    list2.sort(key=lambda x: len(x.getvars()))

                    while len(list2) > 1:
                        p = list2.pop()
                        pivote = min(list2, key=lambda x: len(set(p.getvars()).union(set(x.getvars()))))
                        if len(set(p.getvars()).union(set(pivote.getvars()))) <= Q:
                            h = pivote.combina(p)
                            msize = max(msize, len(h.getvars()))
                            h = h.borra([var])
                            trabajo.insertar(h)
                        else:
                            h = pivote.resolution(p, var)
                            trabajo.insertar(h[0])
                            trabajo.insertar(h[1])
                            r = p.borra([var])
                            trabajo.insertar(r)
                            msize = max(msize, len(h[0].getvars()), len(h[1].getvars()), len(r.getvars()))

                        if trabajo.contradict:
                            break
                    p = list2.pop()
                    r = p.borra([var])
                    trabajo.insertar(r)

            elif list1 or list3:
                listt = list1 + list3
                k = len(listt)
                for i in range(k):
                    r1 = listt[i]
                    for j in range(i + 1, k):
                        r2 = listt[j]
                        (res1, res2) = r2.resolution(r1, var)
                        trabajo.insertar(res1)
                        trabajo.insertar(res2)
                        msize = max(msize, len(res1.getvars()), len(res2.getvars()))

                for p in listt:
                    res.insertars(p)
                    r = p.borra([var])
                    msize = max(msize, len(p.getvars()))
                    trabajo.insertar(r)
                if trabajo.contradict:
                    break

        if self.contradict:
            print("contradict")

        print("tamaño máximo", msize)
        sleep(5)
        res.orden = torden
        return (res, msize)
    
    def addproborden(self):
        for v in self.prob:
            if v not in self.orden:
                self.orden = [v] + self.orden

    def importancesampling(self, N=1000, method=0, K=10):
        borr = self.orden.copy()
        listprobb = []
        listlogic = []
        listprob = []
        oldw = self.w
        sumw = dict()
        for x in borr:
            sumw[x] = 0.0
            sumw[-x] = 0.0

        t1 = time()
        for v in borr:
            for p in self.prob.get(v, []):
                if p not in listprobb:
                    listprobb.append(p)

        for v in borr:
            ll = self.get(v) + self.getd(v)
            ld = self.getd(v)
            listlogic.append(ll)
            for p in ll:
                self.eliminar(p)
            lp = self.prob.get(v, []).copy()

            listprob.append(lp)
            for p in lp:
                self.removebay(p)

            lpc = lp.copy()
            if ld and method == 0:
                for p in lpc:
                    for q in ld:
                        print(q.getvars(), p.getvars())
                        if set(q.getvars()) <= set(p.getvars()):
                            print("Reducción")
                            h = p.combinab(q).borrab([v])
                            self.insertbay(h)
                            lp.remove(p)
                            print("quito ")
                            print(p.tabla)
                            print("añado ")
                            print(h)
                            break

            elif ld and (method == 1 or method == 2):
                piv = min(ld, key=lambda x: len(x.getvars()))
                for p in lpc:
                    print("Reducción")
                    h = p.combinab(piv).borrab([v])
                    self.insertbay(h)
                    lp.remove(p)
                    print("quito ")
                    print(piv.tabla)
                    print("añado ")
                    print(h)

            elif method == 2 and lp:
                h = lp.pop()
                lpc = lp.copy()
                for p in lpc:
                    lp.remove(p)
        
                for p in lpc:
                    if len(set(h.getvars()).union(set(p.getvars()))) <= K:
                        h = h.combinab(p)
                    else:
                        if h.getvars():
                            q = h.borrab([v])
                            self.insertbay(q)
                            t = h.divideb(q)
                            lp.append(t)
                            h = p
                if h.getvars():
                    q = h.borrab([v])
                    self.insertbay(q)
                    t = h.divideb(q)
                    lp.append(t)

        ttotal = 0                        
        borr.reverse()
        listlogic.reverse()
        listprob.reverse()

        pesos = 0.0
        pesos2 = 0.0
        ceros = 0
        
        for j in range(N):
            sol = []
            pe = 1.0
            for i in range(len(borr)):
                var = borr[i]
                ll = listlogic[i]
                lp = listprob[i]
                pos = False
                neg = False
                t1 = time()
                for p in ll:
                    h = p.reduce(sol)
                    if not bool(h.tabla[0]):
                        pos = True
                    if not bool(h.tabla[1]):
                        neg = True

                ttotal += (time() - t1)

                pw = 1.0
                nw = 1.0
                for p in lp:
                    h = p.reduce(sol)
                    nw *= float(h.tabla[0])
                    pw *= float(h.tabla[1])

                if pos and not neg:
                    sol.append(var)
                    pe *= pw

                if neg and not pos:
                    sol.append(-var)
                    pe *= nw
                  
                if not neg and not pos:
                    value = choices([-var, var], weights=[nw, pw])
                    pe *= (nw + pw)
                    sol.append(value[0])

            for x in sol:
                sumw[x] += pe   
                
            if pe == 0:
                ceros += 1
            else:
                pesos += pe
                pesos2 += pe * pe

        print(ttotal)
        print(self.w, pesos)

        pesos = pesos * self.w
        pesos2 = pesos2 * self.w * self.w

        me = pesos / N
        va = pesos2 / N - me * me

        return (ceros, me, va, sumw)