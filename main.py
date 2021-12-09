# Запись строчки в файл, для копирования в один из Resolutions файлов
def WriteResolutions(string):
    global count
    global part

    if count == 5001:
        part += 1
        count = 1

    if part == 1:
        file = open('Resolutions1.txt', 'a')
        file.write('    \item ' + string + '\n')
        file.close()
    elif part == 2:
        file = open('Resolutions2.txt', 'a')
        file.write('    \item ' + string + '\n')
        file.close()
    elif part == 3:
        file = open('Resolutions3.txt', 'a')
        file.write('    \item ' + string + '\n')
        file.close()
    elif part == 4:
        file = open('Resolutions4.txt', 'a')
        file.write('    \item ' + string + '\n')
        file.close()
    elif part == 5:
        file = open('Resolutions5.txt', 'a')
        file.write('    \item ' + string + '\n')
        file.close()
    elif part == 6:
        file = open('Resolutions6.txt', 'a')
        file.write('    \item ' + string + '\n')
        file.close()
    elif part == 7:
        file = open('Resolutions7.txt', 'a')
        file.write('    \item ' + string + '\n')
        file.close()
    elif part == 8:
        file = open('Resolutions8.txt', 'a')
        file.write('    \item ' + string + '\n')
        file.close()
    elif part == 9:
        file = open('Resolutions9.txt', 'a')
        file.write('    \item ' + string + '\n')
        file.close()
    elif part == 10:
        file = open('Resolutions10.txt', 'a')
        file.write('    \item ' + string + '\n')
        file.close()
    count += 1


# Запись строчки в файл, для копирования в Tables файл
def WriteTables(string):
    file = open('Tables.txt', 'a')
    file.write(string + '\n')
    file.close()


# Запись строчки в файл, для копирования в CNF файл
def WriteCNF(string):
    file = open('CNF.txt', 'a')
    file.write(string + '\n')
    file.close()


# Создание таблицы истинности функции ⊕ от пяти переменных, аргументы - названия переменных, вывод в формате LaTex
def XOR5_Table(x1, x2, x3, x4, x5):
    WriteTables('$\,$')
    WriteTables(r'\begin{tabular}[t]{||c|c|c|c|c||c||} \hline')
    WriteTables(r'    ${0}$ & ${1}$ & ${2}$ & ${3}$ & ${4}$ & $ {0} \oplus {1} \oplus {2} \oplus {3} \oplus {4}$\\ \hline \hline'.format(x1, x2, x3, x4, x5))
    for i1 in {0, 1}:
        for i2 in {0, 1}:
            for i3 in {0, 1}:
                for i4 in {0, 1}:
                    for i5 in {0, 1}:
                        WriteTables(r'    ${0}$ & ${1}$ & ${2}$ & ${3}$ & ${4}$ & ${5}$\\ \hline'.format(i1, i2, i3, i4, i5, i1 ^ i2 ^ i3 ^ i4 ^ i5))
    WriteTables('\end{tabular}')
    WriteTables('')


# Закон Де Моргана: из отрицания конъюнкции возвращает дизъюнкцию отрицаний. Все в формате LaTex.
def DeMorganLaw(formula):
    output = ''
    literals = formula.split(r' \wedge ')
    i = 1
    for literal in literals:
        if r'\neg' in literal:
            output += literal.split(r'\neg ')[1]
        else:
            output += r'\neg ' + literal
        if i < 5:
            output += r' \vee '
        i += 1
    return output


# Построение ДНФ для ⊕ от пяти переменных, аргументы - названия переменных, вывод в формате LaTex
def XOR5_DNF(x1, x2, x3, x4, x5):
    WriteTables(' ')
    XOR5_Table(x1, x2, x3, x4, x5)
    WriteTables(' ')

    dnf = []
    for i1 in {0, 1}:
        for i2 in {0, 1}:
            for i3 in {0, 1}:
                for i4 in {0, 1}:
                    for i5 in {0, 1}:
                        conjunct = ''
                        if (i1 ^ i2 ^ i3 ^ i4 ^ i5) == 0:
                            if i1 == 0:
                                conjunct += x1
                            else:
                                conjunct += r'\neg {0}'.format(x1)

                            conjunct += r' \wedge '

                            if i2 == 0:
                                conjunct += x2
                            else:
                                conjunct += r'\neg {0}'.format(x2)

                            conjunct += r' \wedge '

                            if i3 == 0:
                                conjunct += x3
                            else:
                                conjunct += r'\neg {0}'.format(x3)

                            conjunct += r' \wedge '

                            if i4 == 0:
                                conjunct += x4
                            else:
                                conjunct += r'\neg {0}'.format(x4)

                            conjunct += r' \wedge '

                            if i5 == 0:
                                conjunct += x5
                            else:
                                conjunct += r'\neg {0}'.format(x5)
                            dnf.append(conjunct)

    WriteTables('$(' + r') \vee ('.join(dnf) + ')$')
    return dnf


# Построение КНФ для ⊕ от пяти переменных, аргументы - названия переменных, вывод в формате LaTex
def XOR5_CNF(x1, x2, x3, x4, x5):
    WriteTables(' ')
    XOR5_Table(x1, x2, x3, x4, x5)
    WriteTables(' ')

    cnf = []
    for i1 in {0, 1}:
        for i2 in {0, 1}:
            for i3 in {0, 1}:
                for i4 in {0, 1}:
                    for i5 in {0, 1}:
                        disjunct = ''
                        if (i1 ^ i2 ^ i3 ^ i4 ^ i5) == 0:
                            if i1 == 0:
                                disjunct += x1
                            else:
                                disjunct += r'\neg {0}'.format(x1)

                            disjunct += r' \vee '

                            if i2 == 0:
                                disjunct += x2
                            else:
                                disjunct += r'\neg {0}'.format(x2)

                            disjunct += r' \vee '

                            if i3 == 0:
                                disjunct += x3
                            else:
                                disjunct += r'\neg {0}'.format(x3)

                            disjunct += r' \vee '

                            if i4 == 0:
                                disjunct += x4
                            else:
                                disjunct += r'\neg {0}'.format(x4)

                            disjunct += r' \vee '

                            if i5 == 0:
                                disjunct += x5
                            else:
                                disjunct += r'\neg {0}'.format(x5)

                            cnf.append(disjunct)

    WriteTables('$(' + r') \wedge ('.join(cnf) + ')$')

    return '(' + r') \wedge ('.join(cnf) + ')'


# Переводит 5-КНФ в 3-КНФ, вводя новые переменные t с индексами заменяемых переменных
def CNF3(cnf5):
    disjunct_base = cnf5[1:len(cnf5) - 1].split(r') \wedge (')
    output = []
    for disj in disjunct_base:
        d = disj.split(r' \vee ')

        t1 = 't_{%s, \, %s}' % (d[0], d[1])
        t2 = 't_{%s, \, %s}' % (d[3], d[4])

        output.append(r'{0} \vee {1} \vee \neg {2}'.format(d[0], d[1], t1))

        if r'\neg' in d[0]:
            output.append(r'{0} \vee {1}'.format(d[0][5:], t1))
        else:
            output.append(r'\neg {0} \vee {1}'.format(d[0], t1))

        if r'\neg' in d[1]:
            output.append(r'{0} \vee {1}'.format(d[1][5:], t1))
        else:
            output.append(r'\neg {0} \vee {1}'.format(d[1], t1))

        output.append(r'{0} \vee {1} \vee \neg {2}'.format(d[3], d[4], t2))

        if r'\neg' in d[3]:
            output.append(r'{0} \vee {1}'.format(d[3][5:], t1))
        else:
            output.append(r'\neg {0} \vee {1}'.format(d[3], t1))

        if r'\neg' in d[4]:
            output.append(r'{0} \vee {1}'.format(d[4][5:], t1))
        else:
            output.append(r'\neg {0} \vee {1}'.format(d[4], t1))

        output.append(r'{0} \vee {1} \vee {2}'.format(d[2], t1, t2))

    return '(' + r') \wedge ('.join(output) + ')'


# Удаление из БД дизъюктов повторяющихся
def Reduction(cnf):
    base = []
    out = []
    for disj in cnf:
        d = '$'.join(disj)
        base.append(d)
    base = list(set(base))

    for d in base:
        out.append(d.split('$'))

    return out


# Применение метода резолюций ко всем дизъюнктам из cnf1 и cnf2 (их объединению)
def Resolutions(cnf1, cnf2):
    breaker = False
    for n1 in range(len(cnf1)):
        for n2 in range(len(cnf2)):
            ld1 = cnf1[n1]
            ld2 = cnf2[n2]
            oppositeliteral = 0

            for lit in ld1:
                if r'\neg' in lit:
                    if lit[5:] in ld2:
                        oppositeliteral += 1
                        l1 = lit
                        l2 = lit[5:]
                else:
                    if (r'\neg ' + lit) in ld2:
                        oppositeliteral += 1
                        l1 = lit
                        l2 = r'\neg ' + lit

            if oppositeliteral == 1:

                new_disjunct = list(set(ld1 + ld2))

                new_disjunct.remove(l1)
                new_disjunct.remove(l2)

                WriteResolutions('$' + r' \vee '.join(ld1) + ', ' + r' \vee '.join(ld2) + r' \vdash ' + r' \vee '.join(
                    new_disjunct) + '$')

                if len(new_disjunct) == 4:
                    data4.append(new_disjunct)
                elif len(new_disjunct) == 3:
                    data3.append(new_disjunct)
                elif len(new_disjunct) == 2:
                    data2.append(new_disjunct)
                elif len(new_disjunct) == 1:
                    data1.append(new_disjunct)

                elif len(new_disjunct) == 0:
                    print('$' + r' \vee '.join(ld1) + ', ' + r' \vee '.join(ld2) + r' \vdash ' + r' \bot $')
                    breaker = True
            if breaker:
                break
        if breaker:
            print("Finish")
            break


# Очистка файлов вывода

file = open('Tables.txt', 'w')
file.close()

file = open('Resolutions1.txt', 'w')
file.write(r'\begin{enumerate}' + '\n')
file.close()

file = open('Resolutions2.txt', 'w')
file.write(r'\begin{enumerate}' + '\n')
file.close()

file = open('Resolutions3.txt', 'w')
file.write(r'\begin{enumerate}' + '\n')
file.close()

file = open('Resolutions4.txt', 'w')
file.write(r'\begin{enumerate}' + '\n')
file.close()

file = open('Resolutions5.txt', 'w')
file.write(r'\begin{enumerate}' + '\n')
file.close()

file = open('Resolutions6.txt', 'w')
file.write(r'\begin{enumerate}' + '\n')
file.close()

file = open('Resolutions7.txt', 'w')
file.write(r'\begin{enumerate}' + '\n')
file.close()

file = open('Resolutions8.txt', 'w')
file.write(r'\begin{enumerate}' + '\n')
file.close()

file = open('Resolutions9.txt', 'w')
file.write(r'\begin{enumerate}' + '\n')
file.close()

file = open('Resolutions10.txt', 'w')
file.write(r'\begin{enumerate}' + '\n')
file.close()

file = open('CNF.txt', 'w')
file.close()

CNF = '$'

count = 1
part = 1

vertexes = {1: 1, 2: 0, 3: 0, 4: 0, 5: 0, 6: 0}

for k in range(1, 7):
    XOR = []
    type = 'DNF'

    if vertexes[k] == 1:
        for l in range(1, 7):
            if k != l:
                XOR.append('e_{%d, %d}' % (min(k, l), max(k, l)))
                type = "CNF"
    else:
        for l in range(1, 7):
            if k != l:
                XOR.append('e_{%d, %d}' % (min(k, l), max(k, l)))

    if type == 'CNF':
        CNF += CNF3(XOR5_CNF(XOR[0], XOR[1], XOR[2], XOR[3], XOR[4]))
    else:
        CNF += CNF3(
            '(' + r') \wedge ('.join(list(map(DeMorganLaw, XOR5_DNF(XOR[0], XOR[1], XOR[2], XOR[3], XOR[4])))) + ')')
        WriteTables(
            '$(' + r') \wedge ('.join(list(map(DeMorganLaw, XOR5_DNF(XOR[0], XOR[1], XOR[2], XOR[3], XOR[4])))) + ')$')

    if k != 6:
        CNF += ' \wedge '
        
for m in range(1, 7):
    for n in range(1, 7):
        if m % 2 - n % 2 == 0 and m != n:
            CNF += r' \wedge (\neg e_{%d, %d})' % (min(m, n), max(m, n))

WriteCNF('------------------------------')
WriteCNF('            CNF')
WriteCNF('------------------------------')
WriteCNF(CNF + '$')

data = []  # БД всех дизьюктов из полученной 3-КНФ

data4 = []  # БД всех 4-местных дизьюктов
data3 = []  # БД всех 4-местных дизьюктов
data2 = []  # БД всех 4-местных дизьюктов
data1 = []  # БД всех 4-местных дизьюктов


# Заполнение БД всех дизъюнктов
disjunct_data = CNF[2:-1].split(') \wedge (')
for disjunct in disjunct_data:
    data.append(disjunct.split(r' \vee '))


# Применение метода резолюций к исходной КНФ
Resolutions(data, data)



Resolutions(data1, data4)

print('-------')
print(len(data))
print('-------')
data4 = Reduction(data4)
print(len(data4))
data3 = Reduction(data3)
print(len(data3))
data2 = Reduction(data2)
print(len(data2))
data1 = Reduction(data1)
print(len(data1))

Resolutions(data1, data3)

print('-------')
print(len(data))
print('-------')
data4 = Reduction(data4)
print(len(data4))
data3 = Reduction(data3)
print(len(data3))
data2 = Reduction(data2)
print(len(data2))
data1 = Reduction(data1)
print(len(data1))

Resolutions(data2, data3)

print('-------')
print(len(data))
print('-------')
data4 = Reduction(data4)
print(len(data4))
data3 = Reduction(data3)
print(len(data3))
data2 = Reduction(data2)
print(len(data2))
data1 = Reduction(data1)
print(len(data1))

Resolutions(data1, data3)

print('-------')
print(len(data))
print('-------')
data4 = Reduction(data4)
print(len(data4))
data3 = Reduction(data3)
print(len(data3))
data2 = Reduction(data2)
print(len(data2))
data1 = Reduction(data1)
print(len(data1))

Resolutions(data1, data2)

print('-------')
print(len(data))
print('-------')
data4 = Reduction(data4)
print(len(data4))
data3 = Reduction(data3)
print(len(data3))
data2 = Reduction(data2)
print(len(data2))
data1 = Reduction(data1)
print(len(data1))

Resolutions(data1, data1)

print('-------')
print(len(data))
print('-------')
data4 = Reduction(data4)
print(len(data4))
data3 = Reduction(data3)
print(len(data3))
data2 = Reduction(data2)
print(len(data2))
data1 = Reduction(data1)
print(len(data1))

file = open('Resolutions1.txt', 'a')
file.write(r'\end{enumerate}')
file.close()

file = open('Resolutions2.txt', 'a')
file.write(r'\end{enumerate}')
file.close()

file = open('Resolutions3.txt', 'a')
file.write(r'\end{enumerate}')
file.close()

file = open('Resolutions4.txt', 'a')
file.write(r'\end{enumerate}')
file.close()

file = open('Resolutions5.txt', 'a')
file.write(r'\end{enumerate}')
file.close()

file = open('Resolutions6.txt', 'a')
file.write(r'\end{enumerate}')
file.close()

file = open('Resolutions7.txt', 'a')
file.write(r'\end{enumerate}')
file.close()

file = open('Resolutions8.txt', 'a')
file.write(r'\end{enumerate}')
file.close()

file = open('Resolutions9.txt', 'a')
file.write(r'\end{enumerate}')
file.close()

file = open('Resolutions10.txt', 'a')
file.write(r'\end{enumerate}')
file.close()
