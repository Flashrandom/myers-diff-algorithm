import java.io.BufferedOutputStream; // output ko fast likhne ke liye buffer
import java.io.FileDescriptor; // stdout ka descriptor lene ke liye
import java.io.FileOutputStream; // raw bytes seedha stdout par likhne ke liye
import java.io.IOException; // file padhne ke error ke liye
import java.io.OutputStream; // output stream ka type
import java.nio.charset.StandardCharsets; // UTF-8 decode karne ke liye
import java.nio.file.Files; // file ke bytes padhne ke liye
import java.nio.file.Paths; // path banane ke liye
import java.util.Arrays; // fill aur equals ke liye

public class Main { // main class (default package, file ka naam Main.java)

    static int statusCode = 0; // program ka exit code (0 = theek, 2 = file error)

    // ---------------- ek file ki lines ka data ----------------
    static class FileLines { // ek file ki saari lines ko store karta hai
        byte[] rawBytes; // file ke raw bytes
        int n; // lines ki sankhya
        int[] lineBegin; // har line ka start index (data me)
        int[] lineFinish; // har line ka end index (newline ke bina, exclusive)
    }

    // raw bytes ko lines me todta hai (\n par), \r line ka hissa rehta hai
    static FileLines parseLines(byte[] rawBytes) { // file ke bytes input
        FileLines L = new FileLines(); // naya Lines object
        L.rawBytes = rawBytes; // bytes save karo
        int lineTotal = 0; // newline bytes ginne ke liye
        for (byte x : rawBytes) { // har byte par
            if (x == '\n') { // agar newline byte hai
                lineTotal++; // line ginti badhao
            }
        }
        if (rawBytes.length > 0 && rawBytes[rawBytes.length - 1] != '\n') { // agar last byte newline nahi hai
            lineTotal++; // to aakhri line bhi ginni hai (bina newline wali)
        }
        L.n = lineTotal; // total lines
        L.lineBegin = new int[lineTotal]; // start array banao
        L.lineFinish = new int[lineTotal]; // end array banao
        int cursor = 0; // abhi kahan se padh rahe hain
        for (int i = 0; i < lineTotal; i++) { // har line ke liye
            int j = cursor; // line ka end dhundhne ke liye pointer
            while (j < rawBytes.length && rawBytes[j] != '\n') { // jab tak newline na mile
                j++; // aage badho
            }
            L.lineBegin[i] = cursor; // line ka start
            L.lineFinish[i] = j; // line ka end (newline ke bina)
            cursor = j + 1; // agli line newline ke baad shuru hogi
        }
        return L; // Lines return
    }

    // bytes ka hash nikalta hai (lines ko compare karne ke liye)
    static int computeHash(byte[] d, int s, int e) { // data, start, end
        int h = 1; // shuruaati hash
        for (int i = s; i < e; i++) { // har byte par
            h = 31 * h + d[i]; // hash update
        }
        h ^= (h >>> 16); // bits mix karo
        h *= 0x45d9f3b; // aur mix karo
        h ^= (h >>> 16); // aakhri mixing
        return h; // hash return
    }

    // har unique line ko ek integer id deta hai, taaki compare O(1) me ho (int ==
    // int)
    static void assignLineIds(FileLines A, FileLines B, int[] oldLineIds, int[] newLineIds) { // dono files ki lines aur
                                                                                              // id arrays
        int combinedTotal = A.n + B.n; // dono files ki total lines
        int tableSize = 16; // hash table ka minimum size
        while (tableSize < 2 * combinedTotal) { // table ko lines se kam se kam double rakho
            tableSize <<= 1; // power of two banate jao
        }
        int[] hashTable = new int[tableSize]; // table (0 = khali, warna global index + 1)
        int tableMask = tableSize - 1; // index nikalne ka mask
        for (int g = 0; g < combinedTotal; g++) { // har line (A ki phir B ki) par
            FileLines L = (g < A.n) ? A : B; // ye line kis file ki hai
            int li = (g < A.n) ? g : g - A.n; // us file me line ka number
            int s = L.lineBegin[li]; // line ka start
            int e = L.lineFinish[li]; // line ka end
            int slotIndex = computeHash(L.rawBytes, s, e) & tableMask; // table me jagah
            int lineId = -1; // abhi id nahi mili
            while (hashTable[slotIndex] != 0) { // jab tak slot bhara hai
                int h = hashTable[slotIndex] - 1; // us slot wali line ka global index
                FileLines M = (h < A.n) ? A : B; // wo line kis file ki hai
                int mi = (h < A.n) ? h : h - A.n; // us file me number
                if (Arrays.equals(M.rawBytes, M.lineBegin[mi], M.lineFinish[mi], L.rawBytes, s, e)) { // bytes bilkul
                                                                                                      // same hain?
                    lineId = h; // haan, wahi id use karo
                    break; // dhundhna band
                }
                slotIndex = (slotIndex + 1) & tableMask; // agla slot dekho
            }
            if (lineId < 0) { // nayi unique line mili
                hashTable[slotIndex] = g + 1; // slot me save karo
                lineId = g; // iski id wahi global index
            }
            if (g < A.n) { // agar A ki line hai
                oldLineIds[g] = lineId; // A ke id array me
            } else { // warna B ki line hai
                newLineIds[g - A.n] = lineId; // B ke id array me
            }
        }
    }

    // ---------------- MYERS DIFF (linear space, divide and conquer)
    // ----------------
    // kisi bhi int sequence (line ids ya characters) par kaam karta hai
    static class MyersDiff { // diff nikalne wala class
        int[] a; // purani sequence
        int[] b; // nayi sequence
        boolean[] deletedLines; // delA[i] = true matlab a[i] delete hua
        boolean[] insertedLines; // insB[j] = true matlab b[j] insert hua
        int[] forwardPath; // forward V array
        int[] reversePath; // reverse V array
        int diagonalOffset; // negative k ke liye offset

        MyersDiff(int[] a, int[] b) { // constructor
            this.a = a; // purani sequence save
            this.b = b; // nayi sequence save
            deletedLines = new boolean[a.length]; // sab false se shuru
            insertedLines = new boolean[b.length]; // sab false se shuru
            int distanceLimit = (a.length + b.length + 1) / 2 + 2; // d ki upper limit
            diagonalOffset = distanceLimit + 2; // offset
            forwardPath = new int[2 * distanceLimit + 5]; // forward array ek baar banao
            reversePath = new int[2 * distanceLimit + 5]; // reverse array ek baar banao
        }

        void startDiff() { // poori diff chalao
            processRange(0, a.length, 0, b.length); // poori range par solve
        }

        // a[aLo..aHi) aur b[bLo..bHi) ka minimal diff, delA/insB me mark karta hai
        void processRange(int aLo, int aHi, int bLo, int bHi) { // range input
            while (aLo < aHi && bLo < bHi && a[aLo] == b[bLo]) { // shuru ke common elements
                aLo++; // a ka start aage
                bLo++; // b ka start aage
            }
            while (aLo < aHi && bLo < bHi && a[aHi - 1] == b[bHi - 1]) { // ant ke common elements
                aHi--; // a ka end peeche
                bHi--; // b ka end peeche
            }
            if (aLo == aHi) { // a khatam, b me jo bacha wo sab insert
                for (int j = bLo; j < bHi; j++) { // b ke bache elements
                    insertedLines[j] = true; // insert mark karo
                }
                return; // kaam khatam
            }
            if (bLo == bHi) { // b khatam, a me jo bacha wo sab delete
                for (int i = aLo; i < aHi; i++) { // a ke bache elements
                    deletedLines[i] = true; // delete mark karo
                }
                return; // kaam khatam
            }
            int n = aHi - aLo; // a ki length
            int m = bHi - bLo; // b ki length
            int lengthDifference = n - m; // dono ki length ka farak
            boolean checkForward = (lengthDifference & 1) != 0; // delta odd hai to overlap forward pass me milega
            int distanceLimit = (n + m + 1) / 2; // is range ke liye d ki limit
            Arrays.fill(forwardPath, diagonalOffset - distanceLimit - 1, diagonalOffset + distanceLimit + 2, -1); // forward
                                                                                                                  // array
                                                                                                                  // reset
                                                                                                                  // (-1
                                                                                                                  // =
                                                                                                                  // khali)
            Arrays.fill(reversePath, diagonalOffset - distanceLimit - 1, diagonalOffset + distanceLimit + 2, -1); // reverse
                                                                                                                  // array
                                                                                                                  // reset
            forwardPath[diagonalOffset + 1] = 0; // forward ki shuruaat
            reversePath[diagonalOffset + 1] = 0; // reverse ki shuruaat
            int forwardStart = 0; // forward diagonals ki range ghatane ke liye (start)
            int forwardEnd = 0; // forward diagonals ki range ghatane ke liye (end)
            int reverseStart = 0; // reverse diagonals ki range ghatane ke liye (start)
            int reverseEnd = 0; // reverse diagonals ki range ghatane ke liye (end)
            for (int d = 0; d <= distanceLimit; d++) { // d = edits ki sankhya, 0 se badhao
                // ---- forward pass ----
                for (int forwardDiagonal = -d + forwardStart; forwardDiagonal <= d - forwardEnd; forwardDiagonal += 2) { // forward
                                                                                                                         // diagonals
                    int arrayPosition = diagonalOffset + forwardDiagonal; // array index
                    int forwardX; // x coordinate
                    if (forwardDiagonal == -d || (forwardDiagonal != d
                            && forwardPath[arrayPosition - 1] < forwardPath[arrayPosition + 1])) { // upar se aana
                                                                                                   // (insert) behtar?
                        forwardX = forwardPath[arrayPosition + 1]; // insert: x same
                    } else { // warna left se (delete)
                        forwardX = forwardPath[arrayPosition - 1] + 1; // delete: x + 1
                    }
                    int forwardY = forwardX - forwardDiagonal; // y nikalo
                    while (forwardX < n && forwardY < m && a[aLo + forwardX] == b[bLo + forwardY]) { // diagonal par
                                                                                                     // same elements
                        forwardX++; // x aage
                        forwardY++; // y aage
                    }
                    forwardPath[arrayPosition] = forwardX; // is diagonal ka sabse door ka x save
                    if (forwardX > n) { // grid ke bahar nikal gaye
                        forwardEnd += 2; // is side ki diagonal chhod do
                    } else if (forwardY > m) { // grid ke bahar nikal gaye
                        forwardStart += 2; // is side ki diagonal chhod do
                    } else if (checkForward) { // overlap check karna hai
                        int matchingDiagonal = lengthDifference - forwardDiagonal; // reverse ki matching diagonal
                        if (matchingDiagonal >= -distanceLimit && matchingDiagonal <= distanceLimit) { // array ki valid
                                                                                                       // range me hai
                            int reverseReach = reversePath[diagonalOffset + matchingDiagonal]; // reverse ka x (end se
                                                                                               // doori)
                            if (reverseReach != -1 && forwardX >= n - reverseReach) { // forward aur reverse mil gaye
                                processRange(aLo, aLo + forwardX, bLo, bLo + forwardY); // left hissa solve
                                processRange(aLo + forwardX, aHi, bLo + forwardY, bHi); // right hissa solve
                                return; // is range ka kaam khatam
                            }
                        }
                    }
                }
                // ---- reverse pass ----
                for (int reverseDiagonal = -d + reverseStart; reverseDiagonal <= d - reverseEnd; reverseDiagonal += 2) { // reverse
                                                                                                                         // diagonals
                    int arrayPosition = diagonalOffset + reverseDiagonal; // array index
                    int reverseX; // x coordinate (end se doori)
                    if (reverseDiagonal == -d || (reverseDiagonal != d
                            && reversePath[arrayPosition - 1] < reversePath[arrayPosition + 1])) { // upar se aana
                                                                                                   // behtar?
                        reverseX = reversePath[arrayPosition + 1]; // x same
                    } else { // warna left se
                        reverseX = reversePath[arrayPosition - 1] + 1; // x + 1
                    }
                    int reverseY = reverseX - reverseDiagonal; // y nikalo
                    while (reverseX < n && reverseY < m && a[aHi - reverseX - 1] == b[bHi - reverseY - 1]) { // end se
                                                                                                             // same
                                                                                                             // elements
                        reverseX++; // x aage
                        reverseY++; // y aage
                    }
                    reversePath[arrayPosition] = reverseX; // is diagonal ka best x save
                    if (reverseX > n) { // grid ke bahar
                        reverseEnd += 2; // diagonal chhod do
                    } else if (reverseY > m) { // grid ke bahar
                        reverseStart += 2; // diagonal chhod do
                    } else if (!checkForward) { // delta even hai to overlap reverse pass me milega
                        int matchingDiagonal = lengthDifference - reverseDiagonal; // forward ki matching diagonal
                        if (matchingDiagonal >= -distanceLimit && matchingDiagonal <= distanceLimit) { // valid range
                            int forwardReach = forwardPath[diagonalOffset + matchingDiagonal]; // forward ka x
                            if (forwardReach != -1) { // agar wahan forward pahuncha tha
                                int forwardYReach = forwardReach - matchingDiagonal; // forward ka y
                                if (forwardReach >= n - reverseX) { // forward aur reverse mil gaye
                                    processRange(aLo, aLo + forwardReach, bLo, bLo + forwardYReach); // left hissa solve
                                    processRange(aLo + forwardReach, aHi, bLo + forwardYReach, bHi); // right hissa
                                                                                                     // solve
                                    return; // kaam khatam
                                }
                            }
                        }
                    }
                }
            }
            for (int i = aLo; i < aHi; i++) { // (kabhi nahi hona chahiye) safety: sab delete
                deletedLines[i] = true; // delete mark
            }
            for (int j = bLo; j < bHi; j++) { // safety: sab insert
                insertedLines[j] = true; // insert mark
            }
        }
    }

    // ---------------- output ke helpers ----------------
    // ek line likhta hai: prefix + line ke exact bytes + newline
    static void emitLine(OutputStream out, int prefix, FileLines L, int i) throws IOException { // prefix, file, line
                                                                                                // number
        out.write(prefix); // prefix character (' ', '-', '+')
        out.write(L.rawBytes, L.lineBegin[i], L.lineFinish[i] - L.lineBegin[i]); // line ke bytes jaise ke taise
        out.write('\n'); // newline
    }

    // bytes ko Unicode code points me badalta hai (emoji = 1 character)
    static int[] toCodePoints(FileLines L, int i) { // file aur line number
        String s = new String(L.rawBytes, L.lineBegin[i], L.lineFinish[i] - L.lineBegin[i], StandardCharsets.UTF_8); // bytes
                                                                                                                     // se
                                                                                                                     // string
        return s.codePoints().toArray(); // code points ka array
    }

    // true/false flags ko "3-5,9-12" jaisi ranges me badalta hai
    static String makeRanges(boolean[] f) { // changed flags
        StringBuilder builder = new StringBuilder(); // result
        int i = 0; // current position
        while (i < f.length) { // poori array par
            if (f[i]) { // changed character mila
                int j = i; // run ka end dhundhne ke liye
                while (j < f.length && f[j]) { // jab tak changed hain
                    j++; // aage badho
                }
                if (builder.length() > 0) { // agar pehle se range hai
                    builder.append(','); // comma lagao (space nahi)
                }
                builder.append(i).append('-').append(j); // start-end (end shamil nahi)
                i = j; // run ke baad se aage
            } else { // unchanged character
                i++; // aage badho
            }
        }
        return builder.length() == 0 ? "." : builder.toString(); // koi change nahi to "."
    }

    // ---------------- asli kaam ----------------
    static int startDiff(String[] args) { // program ka main logic, exit code return karta hai
        if (args.length != 3 || !(args[0].equals("lines") || args[0].equals("highlight"))) { // galat arguments
            System.err.println("Usage: <program> lines|highlight fileA fileB"); // usage stderr par
            return 2; // error code
        }
        boolean highlightMode = args[0].equals("highlight"); // Part B mode hai ya nahi
        byte[] da; // file A ke bytes
        byte[] db; // file B ke bytes
        try { // files padhne ki koshish
            da = Files.readAllBytes(Paths.get(args[1])); // file A raw bytes me
            db = Files.readAllBytes(Paths.get(args[2])); // file B raw bytes me
        } catch (IOException | RuntimeException e) { // file padh nahi paye
            System.err.println("Error: cannot read file: " + e); // stderr par error message
            return 2; // stdout par kuch nahi, exit code 2
        }
        FileLines A = parseLines(da); // A ki lines
        FileLines B = parseLines(db); // B ki lines
        int[] oldLineIds = new int[A.n]; // A ki lines ke ids
        int[] newLineIds = new int[B.n]; // B ki lines ke ids
        assignLineIds(A, B, oldLineIds, newLineIds); // lines ko integer ids do
        int combinedTotal = A.n + B.n; // ids ki range (0..total-1)
        int[] oldFrequency = new int[combinedTotal]; // har id A me kitni baar aayi
        int[] newFrequency = new int[combinedTotal]; // har id B me kitni baar aayi
        for (int x = 0; x < A.n; x++) { // A ki har line
            oldFrequency[oldLineIds[x]]++; // gino
        }
        for (int x = 0; x < B.n; x++) { // B ki har line
            newFrequency[newLineIds[x]]++; // gino
        }
        int[] oldPositions = new int[A.n]; // A ki wo lines jo B me bhi hain (original index)
        int oldCommonTotal = 0; // unki ginti
        for (int x = 0; x < A.n; x++) { // A ki har line
            if (newFrequency[oldLineIds[x]] > 0) { // agar ye line B me bhi hai
                oldPositions[oldCommonTotal++] = x; // to Myers ke liye rakho
            }
        }
        int[] newPositions = new int[B.n]; // B ki wo lines jo A me bhi hain (original index)
        int newCommonTotal = 0; // unki ginti
        for (int x = 0; x < B.n; x++) { // B ki har line
            if (oldFrequency[newLineIds[x]] > 0) { // agar ye line A me bhi hai
                newPositions[newCommonTotal++] = x; // to Myers ke liye rakho
            }
        }
        int[] oldFiltered = new int[oldCommonTotal]; // A ki filtered sequence (ids)
        for (int x = 0; x < oldCommonTotal; x++) { // filtered A bharo
            oldFiltered[x] = oldLineIds[oldPositions[x]]; // id copy
        }
        int[] newFiltered = new int[newCommonTotal]; // B ki filtered sequence (ids)
        for (int x = 0; x < newCommonTotal; x++) { // filtered B bharo
            newFiltered[x] = newLineIds[newPositions[x]]; // id copy
        }
        MyersDiff df = new MyersDiff(oldFiltered, newFiltered); // sirf common lines par differ (unique lines kabhi
                                                                // match nahi hoti)
        df.startDiff(); // minimal diff nikalo
        boolean[] deletedLines = new boolean[A.n]; // A ki kaun si lines delete hui (original index)
        boolean[] insertedLines = new boolean[B.n]; // B ki kaun si lines insert hui (original index)
        Arrays.fill(deletedLines, true); // jo line sirf A me thi wo delete hi hogi
        Arrays.fill(insertedLines, true); // jo line sirf B me thi wo insert hi hogi
        for (int x = 0; x < oldCommonTotal; x++) { // filtered A ke result wapas original index par
            deletedLines[oldPositions[x]] = df.deletedLines[x]; // Myers ka faisla copy
        }
        for (int x = 0; x < newCommonTotal; x++) { // filtered B ke result wapas original index par
            insertedLines[newPositions[x]] = df.insertedLines[x]; // Myers ka faisla copy
        }
        try { // output likhna
            OutputStream out = new BufferedOutputStream(new FileOutputStream(FileDescriptor.out), 1 << 16); // fast
                                                                                                            // stdout
            int i = 0; // A ki current line
            int j = 0; // B ki current line
            while (i < A.n || j < B.n) { // jab tak dono files khatam na ho
                boolean change = (i < A.n && deletedLines[i]) || (j < B.n && insertedLines[j]); // change block shuru?
                if (change) { // agar change block hai
                    int i2 = i; // deleted lines ka end
                    while (i2 < A.n && deletedLines[i2]) { // lagatar deleted lines
                        i2++; // aage badho
                    }
                    int j2 = j; // inserted lines ka end
                    while (j2 < B.n && insertedLines[j2]) { // lagatar inserted lines
                        j2++; // aage badho
                    }
                    for (int p = i; p < i2; p++) { // pehle saari '-' lines (delete-first rule)
                        emitLine(out, '-', A, p); // delete line likho
                    }
                    for (int q = j; q < j2; q++) { // phir saari '+' lines
                        emitLine(out, '+', B, q); // insert line likho
                        if (highlightMode && (q - j) < (i2 - i)) { // Part B aur is + line ki pair '-' line hai
                            int[] oldCodePoints = toCodePoints(A, i + (q - j)); // pair wali purani line ke characters
                            int[] newCodePoints = toCodePoints(B, q); // nayi line ke characters
                            MyersDiff cd = new MyersDiff(oldCodePoints, newCodePoints); // character-level differ
                            cd.startDiff(); // characters par Myers
                            String rangeLine = "? " + makeRanges(cd.deletedLines) + " | " + makeRanges(cd.insertedLines)
                                    + "\n"; // range wali line
                            out.write(rangeLine.getBytes(StandardCharsets.UTF_8)); // likho
                        }
                    }
                    i = i2; // deleted block ke aage
                    j = j2; // inserted block ke aage
                } else { // keep line (dono files me same)
                    emitLine(out, ' ', A, i); // space prefix ke saath likho
                    i++; // A aage
                    j++; // B aage
                }
            }
            out.flush(); // buffer ka bacha hua output likho
        } catch (IOException e) { // output error
            System.err.println("Error: cannot write output: " + e); // stderr par
            return 2; // error code
        }
        return 0; // sab theek
    }

    public static void main(String[] args) throws Exception { // program yahan se shuru
        Thread t = new Thread(null, () -> statusCode = startDiff(args), "diff", 64L * 1024 * 1024); // bade stack wala
                                                                                                    // thread (recursion
                                                                                                    // ke liye)
        t.start(); // thread chalao
        t.join(); // khatam hone ka intezaar
        System.exit(statusCode); // sahi exit code ke saath band
    }
}