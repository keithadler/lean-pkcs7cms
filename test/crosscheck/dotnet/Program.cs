// .NET: System.Security.Cryptography.Pkcs.SignedCms, CheckSignature(verifySignatureOnly: true).
// One JSON line per case.
using System.Security.Cryptography.Pkcs;
using System.Text.Json;

var dir = args[0];
foreach (var line in File.ReadAllLines(Path.Combine(dir, "manifest.tsv")))
{
    var f = line.Split('\t');
    try
    {
        SignedCms cms = f[2] == "" ? new SignedCms()
            : new SignedCms(new ContentInfo(File.ReadAllBytes(Path.Combine(dir, f[2]))), detached: true);
        cms.Decode(File.ReadAllBytes(Path.Combine(dir, f[1])));
        if (cms.SignerInfos.Count == 0) throw new Exception("no signers");
        cms.CheckSignature(verifySignatureOnly: true);
        Console.WriteLine(JsonSerializer.Serialize(new { id = f[0], ok = true }));
    }
    catch (Exception e)
    {
        Console.WriteLine(JsonSerializer.Serialize(new { id = f[0], ok = false, err = e.GetType().Name + ": " + e.Message.Replace("\n", " ") }));
    }
}
