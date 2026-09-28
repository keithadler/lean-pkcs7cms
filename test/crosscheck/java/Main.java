// Java (OpenJDK): sun.security.pkcs.PKCS7, the parser and verifier jarsigner and the JAR verifier use.
// One JSON line per case: {"id":..., "ok":..., "err":...}.
import java.nio.file.Files;
import java.nio.file.Path;
import sun.security.pkcs.PKCS7;
import sun.security.pkcs.SignerInfo;

public class Main {
    public static void main(String[] args) throws Exception {
        Path dir = Path.of(args[0]);
        for (String line : Files.readAllLines(dir.resolve("manifest.tsv"))) {
            String[] f = line.split("\t", -1);
            String id = f[0];
            try {
                PKCS7 p = new PKCS7(Files.readAllBytes(dir.resolve(f[1])));
                byte[] content = f[2].isEmpty() ? null : Files.readAllBytes(dir.resolve(f[2]));
                SignerInfo[] ok = p.verify(content);
                int n = p.getSignerInfos() == null ? 0 : p.getSignerInfos().length;
                if (ok == null || ok.length == 0 || ok.length != n) throw new Exception("verify returned " + (ok == null ? "null" : ok.length + " of " + n));
                System.out.println("{\"id\":\"" + id + "\",\"ok\":true}");
            } catch (Throwable e) {
                String msg = (e.getClass().getSimpleName() + ": " + e.getMessage()).replace("\\", "\\\\").replace("\"", "'");
                System.out.println("{\"id\":\"" + id + "\",\"ok\":false,\"err\":\"" + msg.replace("\n", " ") + "\"}");
            }
        }
    }
}
