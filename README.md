# NXDOMAIN'd

| Browser                                                                                                                                                                                                 | Install from                                                                                        |
| ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------- |
| <a href="https://addons.mozilla.org/firefox/addon/nxdomaind/"><img src="https://cdn.jsdelivr.net/gh/alrra/browser-logos@75.0.1/src/firefox/firefox_64x64.png" width="32" height="32" alt="Firefox"></a> | [Firefox Add-ons](https://addons.mozilla.org/firefox/addon/nxdomaind/)                              |
| <img src="https://cdn.jsdelivr.net/gh/alrra/browser-logos@75.0.1/src/chrome/chrome_64x64.png" width="32" height="32" alt="Chrome">                                                                      | [GitHub Releases](../../releases/latest), loaded unpacked (see [Other downloads](#other-downloads)) |

**Discover dangling unregistered domains while browsing the web.**

Looking to perform a supply-chain attack? Look no further! This extension allows you to automatically discover websites which are loading resources from domains which you can register today!

Do you want to do any of the following?

- Show your own ads,
- Rewrite links for your affiliate programs,
- DDoS,
- Access user data,
- Show FAKE NEWS,
- Mine crypto in the browser
- ... and more?

Well, then this script may be for you!

Note: don't do any of the above things if you care about the law, of course!

## What it actually does

- Monitors all network requests, and extracts all connected-to ICANN-only **domain** (using the [PSL](https://publicsuffix.org/) with [tldts](https://www.npmjs.com/package/tldts)).
- Uses either **RDAP** or **DNS-over-HTTPS** to check if the domain is actually registered, or it's an unregistered, dangling domain.
- Records the **page URL** (where the request was initiated from) and the **full request URL** (where the request was supposed to be made to).
- Listens for CSP violations too, since requests blocked by a page's CSP never reach `webRequest`.
- The extension badge turns **red** on new finding; **blue** when idle; and **yellow** while checking new domains.

The idea is that there some websites attempting to load resources from external domains which no longer exist. You can register them, and take advantage of how the external resource is being loaded.

## Other downloads

Releases also have these files:

- `nxdomain-watcher-firefox.xpi`, signed by Mozilla. Drag it into a Firefox window, or open `about:addons`, click the gear and choose Install Add-on From File. If a release only has `nxdomain-watcher-firefox.unsigned.xpi`, Mozilla hadn't signed it yet. Only Firefox Developer Edition and Nightly install that, after you set `xpinstall.signatures.required` to `false` in `about:config`.
- `nxdomain-watcher-chrome.zip`. Unzip it, open `chrome://extensions`, turn on Developer mode, click Load unpacked and pick the unzipped folder.

## Privacy

NXDOMAIN'd has no accounts, analytics or tracking. To check whether a domain is registered, it sends just the domain name to public RDAP and DNS-over-HTTPS services. See [PRIVACY.md](PRIVACY.md).

## Issues

Report problems in [Issues](../../issues).

## Changelog

See [Releases](../../releases).

## Development

Building, loading a local build and tuning are in [DEVELOPMENT.md](DEVELOPMENT.md).
